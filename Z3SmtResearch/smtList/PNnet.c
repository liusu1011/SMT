#include<stdio.h>
#include<stdlib.h>
#include<stdarg.h>
#include<memory.h>
#include<setjmp.h>
#include<z3.h>

#define LOG_Z3_CALLS

#ifdef LOG_Z3_CALLS
#define LOG_MSG(msg) Z3_append_log(msg)
#else
#define LOG_MSG(msg) ((void)0)
#endif

/**
   \defgroup capi_ex C API examples
*/
/*@{*/
/**
   @name Auxiliary Functions
*/
/*@{*/

/**
   \brief exit gracefully in case of error.
*/
void exitf(const char* message)
{
  fprintf(stderr,"BUG: %s.\n", message);
  exit(1);
}

/**
   \brief exit if unreachable code was reached.
*/
void unreachable()
{
    exitf("unreachable code was reached");
}

/**
   \brief Simpler error handler.
 */
void error_handler(Z3_context c, Z3_error_code e)
{
    printf("Error code: %d\n", e);
    exitf("incorrect use of Z3");
}

static jmp_buf g_catch_buffer;
/**
   \brief Low tech exceptions.

   In high-level programming languages, an error handler can throw an exception.
*/
void throw_z3_error(Z3_context c, Z3_error_code e)
{
    longjmp(g_catch_buffer, e);
}

/**
   \brief Display the given type.
*/
void display_sort(Z3_context c, FILE * out, Z3_sort ty)
{
    switch (Z3_get_sort_kind(c, ty)) {
    case Z3_UNINTERPRETED_SORT:
        display_symbol(c, out, Z3_get_sort_name(c, ty));
        break;
    case Z3_BOOL_SORT:
        fprintf(out, "bool");
        break;
    case Z3_INT_SORT:
        fprintf(out, "int");
        break;
    case Z3_REAL_SORT:
        fprintf(out, "real");
        break;
    case Z3_BV_SORT:
        fprintf(out, "bv%d", Z3_get_bv_sort_size(c, ty));
        break;
    case Z3_ARRAY_SORT:
        fprintf(out, "[");
        display_sort(c, out, Z3_get_array_sort_domain(c, ty));
        fprintf(out, "->");
        display_sort(c, out, Z3_get_array_sort_range(c, ty));
        fprintf(out, "]");
        break;
    case Z3_DATATYPE_SORT:
		if (Z3_get_datatype_sort_num_constructors(c, ty) != 1)
		{
			fprintf(out, "%s", Z3_sort_to_string(c,ty));
			break;
		}
		{
        unsigned num_fields = Z3_get_tuple_sort_num_fields(c, ty);
        unsigned i;
        fprintf(out, "(");
        for (i = 0; i < num_fields; i++) {
            Z3_func_decl field = Z3_get_tuple_sort_field_decl(c, ty, i);
            if (i > 0) {
                fprintf(out, ", ");
            }
            display_sort(c, out, Z3_get_range(c, field));
        }
        fprintf(out, ")");
        break;
    }
    default:
        fprintf(out, "unknown[");
        display_symbol(c, out, Z3_get_sort_name(c, ty));
        fprintf(out, "]");
        break;
    }
}

/**
   \brief Display a symbol in the given output stream.
*/
void display_symbol(Z3_context c, FILE * out, Z3_symbol s)
{
    switch (Z3_get_symbol_kind(c, s)) {
    case Z3_INT_SYMBOL:
        fprintf(out, "#%d", Z3_get_symbol_int(c, s));
        break;
    case Z3_STRING_SYMBOL:
        fprintf(out, "%s", Z3_get_symbol_string(c, s));
        break;
    default:
        unreachable();
    }
}

/**
   \brief Create a logical context.

   Enable model construction. Other configuration parameters can be passed in the cfg variable.

   Also enable tracing to stderr and register custom error handler.
*/
Z3_context mk_context_custom(Z3_config cfg, Z3_error_handler err)
{
    Z3_context ctx;

    Z3_set_param_value(cfg, "MODEL", "true");
    ctx = Z3_mk_context(cfg);
    Z3_set_error_handler(ctx, err);

    return ctx;
}

/**
   \brief Create a logical context.

   Enable model construction only.

   Also enable tracing to stderr and register standard error handler.
*/
Z3_context mk_context()
{
    Z3_config  cfg;
    Z3_context ctx;
    cfg = Z3_mk_config();
    Z3_set_param_value(cfg, "MODEL", "true");
    ctx = mk_context_custom(cfg, error_handler);
    return ctx;
}

/**
   \brief Create a logical context.

   Enable fine-grained proof construction.
   Enable model construction.

   Also enable tracing to stderr and register standard error handler.
*/
Z3_context mk_proof_context() {
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx;
    Z3_set_param_value(cfg, "PROOF_MODE", "2");
    ctx = mk_context_custom(cfg, throw_z3_error);
    Z3_del_config(cfg);
    return ctx;
}

/**
   \brief Create a variable using the given name and type.
*/
Z3_ast mk_var(Z3_context ctx, const char * name, Z3_sort ty)
{
    Z3_symbol   s  = Z3_mk_string_symbol(ctx, name);
    return Z3_mk_const(ctx, s, ty);
}

/**
   \brief Create a boolean variable using the given name.
*/
Z3_ast mk_bool_var(Z3_context ctx, const char * name)
{
    Z3_sort ty = Z3_mk_bool_sort(ctx);
    return mk_var(ctx, name, ty);
}

/**
   \brief Create an integer variable using the given name.
*/
Z3_ast mk_int_var(Z3_context ctx, const char * name)
{
    Z3_sort ty = Z3_mk_int_sort(ctx);
    return mk_var(ctx, name, ty);
}

/**
   \brief Create a Z3 integer node using a C int.
*/
Z3_ast mk_int(Z3_context ctx, int v)
{
    Z3_sort ty = Z3_mk_int_sort(ctx);
    return Z3_mk_int(ctx, v, ty);
}

/**
   \brief Create a real variable using the given name.
*/
Z3_ast mk_real_var(Z3_context ctx, const char * name)
{
    Z3_sort ty = Z3_mk_real_sort(ctx);
    return mk_var(ctx, name, ty);
}

/**
   \brief Create the unary function application: <tt>(f x)</tt>.
*/
Z3_ast mk_unary_app(Z3_context ctx, Z3_func_decl f, Z3_ast x)
{
    Z3_ast args[1] = {x};
    return Z3_mk_app(ctx, f, 1, args);
}

/**
   \brief Create the binary function application: <tt>(f x y)</tt>.
*/
Z3_ast mk_binary_app(Z3_context ctx, Z3_func_decl f, Z3_ast x, Z3_ast y)
{
    Z3_ast args[2] = {x, y};
    return Z3_mk_app(ctx, f, 2, args);
}

/**
   \brief Z3 does not support explicitly tuple updates. They can be easily implemented
   as macros. The argument \c t must have tuple type.
   A tuple update is a new tuple where field \c i has value \c new_val, and all
   other fields have the value of the respective field of \c t.

   <tt>update(t, i, new_val)</tt> is equivalent to
   <tt>mk_tuple(proj_0(t), ..., new_val, ..., proj_n(t))</tt>
*/
Z3_ast mk_tuple_update(Z3_context c, Z3_ast t, unsigned i, Z3_ast new_val)
{
    Z3_sort         ty;
    Z3_func_decl   mk_tuple_decl;
    unsigned            num_fields, j;
    Z3_ast *            new_fields;
    Z3_ast              result;

    ty = Z3_get_sort(c, t);

    if (Z3_get_sort_kind(c, ty) != Z3_DATATYPE_SORT) {
        exitf("argument must be a tuple");
    }

    num_fields = Z3_get_tuple_sort_num_fields(c, ty);

    if (i >= num_fields) {
        exitf("invalid tuple update, index is too big");
    }

    new_fields = (Z3_ast*) malloc(sizeof(Z3_ast) * num_fields);
    for (j = 0; j < num_fields; j++) {
        if (i == j) {
            /* use new_val at position i */
            new_fields[j] = new_val;
        }
        else {
            /* use field j of t */
            Z3_func_decl proj_decl = Z3_get_tuple_sort_field_decl(c, ty, j);
            new_fields[j] = mk_unary_app(c, proj_decl, t);
        }
    }
    mk_tuple_decl = Z3_get_tuple_sort_mk_decl(c, ty);
    result = Z3_mk_app(c, mk_tuple_decl, num_fields, new_fields);
    free(new_fields);
    return result;
}


/**
   \brief Check whether the logical context is satisfiable, and compare the result with the expected result.
   If the context is satisfiable, then display the model.
*/
void check(Z3_context ctx, Z3_lbool expected_result)
{
    Z3_model m      = 0;
    Z3_lbool result = Z3_check_and_get_model(ctx, &m);

    printf("\nThe checking result is:%i\n", result);
    switch (result) {
    case Z3_L_FALSE:
        printf("unsat\n");
        break;
    case Z3_L_UNDEF:
        printf("unknown\n");
        printf("potential model:\n%s\n", Z3_model_to_string(ctx, m));
        break;
    case Z3_L_TRUE:
        printf("sat\n%s\n", Z3_model_to_string(ctx, m));
        break;
    }
    if (m) {
//    	printf("\ndelete model.");
        Z3_del_model(ctx, m);
    }
    if (result != expected_result) {
//        exitf("unexpected result");
    }
}

/**
   \brief Prove that the constraints already asserted into the logical
   context implies the given formula.  The result of the proof is
   displayed.

   Z3 is a satisfiability checker. So, one can prove \c f by showing
   that <tt>(not f)</tt> is unsatisfiable.

   The context \c ctx is not modified by this function.
*/
void prove(Z3_context ctx, Z3_ast f, Z3_bool is_valid)
{
    Z3_model m;
    Z3_ast   not_f;

    /* save the current state of the context */
    Z3_push(ctx);

    not_f = Z3_mk_not(ctx, f);
    Z3_assert_cnstr(ctx, not_f);

    m = 0;

    switch (Z3_check_and_get_model(ctx, &m)) {
    case Z3_L_FALSE:
        /* proved */
        printf("valid\n");
        if (!is_valid) {
            exitf("unexpected result");
        }
        break;
    case Z3_L_UNDEF:
        /* Z3 failed to prove/disprove f. */
        printf("unknown\n");
        if (m != 0) {
            /* m should be viewed as a potential counterexample. */
            printf("potential counterexample:\n%s\n", Z3_model_to_string(ctx, m));
        }
        if (is_valid) {
            exitf("unexpected result");
        }
        break;
    case Z3_L_TRUE:
        /* disproved */
        printf("invalid\n");
        if (m) {
            /* the model returned by Z3 is a counterexample */
            printf("counterexample:\n%s\n", Z3_model_to_string(ctx, m));
        }
        if (is_valid) {
            exitf("unexpected result");
        }
        break;
    }

    if (m) {
        Z3_del_model(ctx, m);
    }

    /* restore context */
    Z3_pop(ctx, 1);
}

/**
   \brief Assert the axiom: function f is injective in the i-th argument.

   The following axiom is asserted into the logical context:
   \code
   forall (x_0, ..., x_n) finv(f(x_0, ..., x_i, ..., x_{n-1})) = x_i
   \endcode

   Where, \c finv is a fresh function declaration.
*/
void assert_inj_axiom(Z3_context ctx, Z3_func_decl f, unsigned i)
{
    unsigned sz, j;
    Z3_sort finv_domain, finv_range;
    Z3_func_decl finv;
    Z3_sort * types; /* types of the quantified variables */
    Z3_symbol *   names; /* names of the quantified variables */
    Z3_ast * xs;         /* arguments for the application f(x_0, ..., x_i, ..., x_{n-1}) */
    Z3_ast   x_i, fxs, finv_fxs, eq;
    Z3_pattern p;
    Z3_ast   q;
    sz = Z3_get_domain_size(ctx, f);

    if (i >= sz) {
        exitf("failed to create inj axiom");
    }

    /* declare the i-th inverse of f: finv */
    finv_domain = Z3_get_range(ctx, f);
    finv_range  = Z3_get_domain(ctx, f, i);
    finv        = Z3_mk_fresh_func_decl(ctx, "inv", 1, &finv_domain, finv_range);

    /* allocate temporary arrays */
    types       = (Z3_sort *) malloc(sizeof(Z3_sort) * sz);
    names       = (Z3_symbol *) malloc(sizeof(Z3_symbol) * sz);
    xs          = (Z3_ast *) malloc(sizeof(Z3_ast) * sz);

    /* fill types, names and xs */
    for (j = 0; j < sz; j++) { types[j] = Z3_get_domain(ctx, f, j); };
    for (j = 0; j < sz; j++) { names[j] = Z3_mk_int_symbol(ctx, j); };
    for (j = 0; j < sz; j++) { xs[j]    = Z3_mk_bound(ctx, j, types[j]); };

    x_i = xs[i];

    /* create f(x_0, ..., x_i, ..., x_{n-1}) */
    fxs         = Z3_mk_app(ctx, f, sz, xs);

    /* create f_inv(f(x_0, ..., x_i, ..., x_{n-1})) */
    finv_fxs    = mk_unary_app(ctx, finv, fxs);

    /* create finv(f(x_0, ..., x_i, ..., x_{n-1})) = x_i */
    eq          = Z3_mk_eq(ctx, finv_fxs, x_i);

    /* use f(x_0, ..., x_i, ..., x_{n-1}) as the pattern for the quantifier */
    p           = Z3_mk_pattern(ctx, 1, &fxs);
    printf("pattern: %s\n", Z3_pattern_to_string(ctx, p));
    printf("\n");

    /* create & assert quantifier */
    q           = Z3_mk_forall(ctx,
                                 0, /* using default weight */
                                 1, /* number of patterns */
                                 &p, /* address of the "array" of patterns */
                                 sz, /* number of quantified variables */
                                 types,
                                 names,
                                 eq);
    printf("assert axiom:\n%s\n", Z3_ast_to_string(ctx, q));
    Z3_assert_cnstr(ctx, q);

    /* free temporary arrays */
    free(types);
    free(names);
    free(xs);
}

/**
   \brief Assert the axiom: function f is commutative.

   This example uses the SMT-LIB parser to simplify the axiom construction.
*/
void assert_comm_axiom(Z3_context ctx, Z3_func_decl f)
{
    Z3_sort t;
    Z3_symbol f_name, t_name;
    Z3_ast q;

    t = Z3_get_range(ctx, f);

    if (Z3_get_domain_size(ctx, f) != 2 ||
        Z3_get_domain(ctx, f, 0) != t ||
        Z3_get_domain(ctx, f, 1) != t) {
        exitf("function must be binary, and argument types must be equal to return type");
    }

    /* Inside the parser, function f will be referenced using the symbol 'f'. */
    f_name = Z3_mk_string_symbol(ctx, "f");

    /* Inside the parser, type t will be referenced using the symbol 'T'. */
    t_name = Z3_mk_string_symbol(ctx, "T");


    Z3_parse_smtlib_string(ctx,
                           "(benchmark comm :formula (forall (x T) (y T) (= (f x y) (f y x))))",
                           1, &t_name, &t,
                           1, &f_name, &f);
    q = Z3_get_smtlib_formula(ctx, 0);
    printf("assert axiom:\n%s\n", Z3_ast_to_string(ctx, q));
    Z3_assert_cnstr(ctx, q);
}

int encode(int i){

	return 0;
}

int *decode(int d){

	return 0;
}

void simple_example()
{
    Z3_context ctx;
    LOG_MSG("simple_example");
    printf("\nsimple_example\n");

    ctx = mk_context();

    /* do something with the context */
    printf("CONTEXT:\n%sEND OF CONTEXT\n", Z3_context_to_string(ctx));
    /* delete logical context */
    Z3_del_context(ctx);
}

void array_example3()
{
    Z3_context ctx;
    Z3_sort bool_sort, int_sort, array_sort;
    Z3_sort domain, range;
    printf("\narray_example3\n");
    LOG_MSG("array_example3");

    ctx      = mk_context();

    bool_sort  = Z3_mk_bool_sort(ctx);
    int_sort   = Z3_mk_int_sort(ctx);
    array_sort = Z3_mk_array_sort(ctx, int_sort, bool_sort);

    if (Z3_get_sort_kind(ctx, array_sort) != Z3_ARRAY_SORT) {
        exitf("type must be an array type");
    }

    domain = Z3_get_array_sort_domain(ctx, array_sort);
    range  = Z3_get_array_sort_range(ctx, array_sort);

    printf("domain: ");
    display_sort(ctx, stdout, domain);
    printf("\n");
    printf("range:  ");
    display_sort(ctx, stdout, range);
    printf("\n");

	if (int_sort != domain || bool_sort != range) {
        exitf("invalid array type");
    }

    Z3_del_context(ctx);
}

void list_framework_first_model(Z3_context ctx)
{
    //declaration for building state tuple
    Z3_sort int_sort;
    Z3_sort places_sort;
    Z3_symbol mk_tuple_name;
    Z3_symbol proj_names[3];
    Z3_sort proj_sorts[3];
    Z3_func_decl  mk_tuple_decl;
    Z3_func_decl  proj_decls[3];
    Z3_func_decl get_place0_decl, get_place1_decl, get_place2_decl;

    Z3_ast zero  = mk_int(ctx, 0);
	Z3_ast one = mk_int(ctx, 1);
	Z3_ast two = mk_int(ctx, 2);
	Z3_ast ten  = mk_int(ctx, 10);

    //declaration for building list datatype
    Z3_func_decl nil_decl, is_nil_decl, cons_decl, is_cons_decl, head_decl, tail_decl;

    LOG_MSG("build a list_framework");
	printf("\nbuild a list_framework: first model\n");

	//build a state tuple as a sort


			mk_tuple_name = Z3_mk_string_symbol(ctx, "mk_places");

			proj_names[0] = Z3_mk_string_symbol(ctx, "place0");
			proj_names[1] = Z3_mk_string_symbol(ctx, "place1");
			proj_names[2] = Z3_mk_string_symbol(ctx, "place2");

			int_sort = Z3_mk_int_sort(ctx);
			proj_sorts[0] = int_sort;
			proj_sorts[1] = int_sort;
			proj_sorts[2] = int_sort;

			places_sort = Z3_mk_tuple_sort(ctx, mk_tuple_name, 3, proj_names, proj_sorts, &mk_tuple_decl, proj_decls);
			get_place0_decl = proj_decls[0];
			get_place1_decl = proj_decls[1];
			get_place2_decl = proj_decls[2];

	//build a list with state as an list element
			Z3_sort pn_list = Z3_mk_list_sort(ctx, Z3_mk_string_symbol(ctx, "pn_list"), places_sort,
					&nil_decl, &is_nil_decl, &cons_decl, &is_cons_decl, &head_decl, &tail_decl);

			//declare initial state in a list
//			Z3_ast initial_state = mk_var(ctx, "ini_st", places_sort);
			Z3_ast states = mk_var(ctx, "states", pn_list); //declare a new list "PN_List"
			Z3_ast is_cons_states = mk_unary_app(ctx, is_cons_decl, states); //is cons(states)

			Z3_ast head = mk_unary_app(ctx, head_decl, states);// states list head
			Z3_ast head_place0 = mk_unary_app(ctx, get_place0_decl, head); // PN_List's head-> tuple's 'place0'
			Z3_ast head_place1 = mk_unary_app(ctx, get_place1_decl, head); // PN_List's head-> tuple's 'place1'
			Z3_ast head_place2 = mk_unary_app(ctx, get_place2_decl, head); // PN_List's head-> tuple's 'place2'

			//initial condition
			Z3_ast ini_and[3] = {Z3_mk_eq(ctx, head_place0, zero),
					Z3_mk_eq(ctx, head_place1, zero), Z3_mk_eq(ctx, head_place2, one)};
			Z3_ast initial_condition = Z3_mk_and(ctx, 3, ini_and);

//
//			//assert a value 1 to place2 in initial state
//			Z3_ast assert_p2_val = Z3_mk_eq(ctx, head_place2, one);
//			Z3_assert_cnstr(ctx, assert_p2_val);

			//define check_transition function

						//function symbol "check_tr"
						Z3_symbol check_tr_func_symbol = Z3_mk_string_symbol (ctx, "check_tr");
					    Z3_sort check_tr_arg_sorts[1] = {pn_list};

					    Z3_sort check_tr_return_sort = Z3_mk_bool_sort(ctx);
					    unsigned domain_size = 1;

						Z3_func_decl check_tr =
								Z3_mk_func_decl(ctx, check_tr_func_symbol, domain_size, check_tr_arg_sorts, check_tr_return_sort);

						//forall axiom elements
						Z3_ast x = Z3_mk_bound(ctx, 0, pn_list); // x is list variable in quantifier
						Z3_ast check_tr_x = Z3_mk_app(ctx, check_tr, 1, &x);
						Z3_pattern pattern = Z3_mk_pattern(ctx, 1, &check_tr_x); //pattern
						Z3_symbol someName = Z3_mk_int_symbol(ctx, 0);

						Z3_ast head_x = mk_unary_app(ctx, head_decl, x);// x's head
						Z3_ast head_x_place2 = mk_unary_app(ctx, get_place2_decl, head_x);
						Z3_ast head_gt_zero = Z3_mk_gt(ctx, head_x_place2, zero);
						Z3_ast head_lt_ten = Z3_mk_lt(ctx, head_x_place2, ten);
						Z3_ast toCAnd[2] = {head_gt_zero, head_lt_ten};
						Z3_ast head_and_cond = Z3_mk_and(ctx, 2, toCAnd); //10 > headplace2 > 0

//						Z3_bool ite_bool_cond = head_gt_zero;
						Z3_ast tail_x = mk_unary_app(ctx, tail_decl, x);
						Z3_ast tail_head = mk_unary_app(ctx, head_decl, tail_x);
						Z3_ast tail_x_place2 = mk_unary_app(ctx, get_place2_decl, tail_head);
						Z3_ast toSum[2] = {head_x_place2, one};//head.place2 + 1
						Z3_ast tailhead_plusone = Z3_mk_add(ctx, 2, toSum);

//						Z3_ast tailhead_unchange = Z3_mk_eq(ctx, tail_x_place2, head_x_place2);
						Z3_ast transition_condition = Z3_mk_ite(ctx, head_and_cond,
								Z3_mk_eq(ctx, tail_x_place2, tailhead_plusone),
								Z3_mk_eq(ctx, tail_x_place2, head_x_place2)); //transition condition

						Z3_ast twelve  = mk_int(ctx, 12);
						Z3_ast eleven  = mk_int(ctx, 11);
						Z3_ast nine  = mk_int(ctx, 9);
						Z3_ast eight  = mk_int(ctx, 8);

						Z3_ast error_condition_eq_eight = Z3_mk_eq(ctx, tail_x_place2, eight); //error property ite's condition
//						Z3_ast error_condition_tail_lt_ten = Z3_mk_lt(ctx, tail_x_place2, ten); //error property ite's condition

						Z3_ast tail_tail_lst = mk_unary_app(ctx, tail_decl, tail_x);
						Z3_ast is_nil_tail = mk_unary_app(ctx, is_nil_decl, tail_tail_lst);
						Z3_ast is_cons_tail = mk_unary_app(ctx, is_cons_decl, tail_tail_lst);
						Z3_ast property_axiom = Z3_mk_ite(ctx, error_condition_eq_eight, is_nil_tail, is_cons_tail);//property axiom
						Z3_ast check_tr_tail_list = mk_unary_app(ctx, check_tr, tail_x); //check_tr(tail(lst));

						Z3_ast is_cons_lst = mk_unary_app(ctx, is_cons_decl, x); //is_cons(lst)
						Z3_ast is_cons_tail_lst = mk_unary_app(ctx, is_cons_decl, tail_x); //is_cons(tail(lst))
						Z3_ast toCondAnd[2] = {is_cons_lst, is_cons_tail_lst};
						Z3_ast axiomTree_cond = Z3_mk_and(ctx, 2, toCondAnd); //(is cons(lst) ^ is cons(tail(lst)))
						Z3_ast toBigAnd[3] = {transition_condition, check_tr_tail_list, property_axiom};
						Z3_ast axiomTree_true = Z3_mk_and(ctx, 3, toBigAnd);
						Z3_ast axiomTree_false = Z3_mk_false(ctx);

						Z3_ast axiomTree =
								Z3_mk_ite(ctx, axiomTree_cond, axiomTree_true, axiomTree_false);//the big if body in forall axiom

						Z3_ast check_tr_forall_axiom =
								Z3_mk_quantifier(ctx, Z3_TRUE, 0, 1, &pattern, 1, &pn_list, &someName, axiomTree);//the body of check_tr

						Z3_assert_cnstr(ctx, check_tr_forall_axiom);
						Z3_ast check_tr_states = mk_unary_app(ctx, check_tr, states);
			//logic context assert
			Z3_ast assertAnd[3] = {is_cons_states, initial_condition, check_tr_states};
			Z3_ast assertCtx = Z3_mk_and(ctx, 3, assertAnd);
			Z3_assert_cnstr(ctx, assertCtx);
}

/**
 * Jan 22nd 2013
 */
Z3_ast mk_add(Z3_context ctx, Z3_ast left, Z3_ast right){
	Z3_ast toSum[2] = {left, right};
	return Z3_mk_add(ctx, 2, toSum);
}

Z3_ast mk_sub(Z3_context ctx, Z3_ast left, Z3_ast right){
	Z3_ast toMinus[2] = {left, right};
	return Z3_mk_sub(ctx, 2, toMinus);
}

Z3_ast mk_and(Z3_context ctx, Z3_ast left, Z3_ast right){
	Z3_ast toAnd[2] = {left, right};
	return Z3_mk_and(ctx, 2, toAnd);
}

Z3_ast mk_or(Z3_context ctx, Z3_ast left, Z3_ast right){
	Z3_ast toOr[2] = {left, right};
	return Z3_mk_or(ctx, 2, toOr);
}

void array_model(Z3_context ctx){

			LOG_MSG("testing ARRAY model ......");
			printf("\n testing ARRAY model....\n");

			//declare int_sort
			Z3_sort int_sort = Z3_mk_int_sort(ctx);

			/**
			 * declare integers
			 */
			unsigned p1_c = 0;
			unsigned p2_c = 0;

			Z3_ast default_val = Z3_mk_int(ctx, -1, int_sort);
			Z3_ast zero = Z3_mk_int(ctx, 0, int_sort);
			Z3_ast one = Z3_mk_int(ctx, 1, int_sort);
			Z3_ast two = Z3_mk_int(ctx, 2, int_sort);
			Z3_ast three = Z3_mk_int(ctx, 3, int_sort);
			Z3_ast four = Z3_mk_int(ctx, 4, int_sort);
			Z3_ast five = Z3_mk_int(ctx, 5, int_sort);

			/**
			 * make a tuple sort
			 * can make more sorts for [int], [int,int], [int,int,int].... for place type use
			 */
			Z3_symbol mk_tuple_p1;
			Z3_symbol p1_names[2];
		    Z3_sort p1_sorts[2];
		    Z3_func_decl  mk_p1_decl;
		    Z3_func_decl  p1_proj_decls[2];
		    Z3_func_decl p1_field0_decl, p1_field1_decl;
		    Z3_func_decl p2_field0_decl, p2_field1_decl;

		    mk_tuple_p1 = Z3_mk_string_symbol(ctx, "mk_p1");
		    p1_names[0] = Z3_mk_string_symbol(ctx, "p1_field1");
		    p1_names[1] = Z3_mk_string_symbol(ctx, "p2_field2");
		    p1_sorts[0] = int_sort;
		    p1_sorts[1] = int_sort;

		    Z3_sort p1_placetype_sort =
		    		Z3_mk_tuple_sort(ctx, mk_tuple_p1, 2, p1_names, p1_sorts, &mk_p1_decl, p1_proj_decls);

		    p1_field0_decl = p1_proj_decls[0];
		    p1_field1_decl = p1_proj_decls[1];


		    /**
		     * declare places array sort
		     * initial places arrays and their indices
		     */
		    Z3_sort p1_array_sort = Z3_mk_array_sort(ctx, int_sort, p1_placetype_sort);
		    Z3_sort p2_array_sort = Z3_mk_array_sort(ctx, int_sort, p1_placetype_sort);


//		    Z3_ast p1_i0 = mk_int(ctx, 0);
			Z3_ast p2_0 = mk_var(ctx, "p2", p2_array_sort);
			Z3_ast p2_i0 = mk_var(ctx, "p2_i0_counter", int_sort);
			Z3_assert_cnstr(ctx, Z3_mk_eq(ctx, p2_i0, zero));
//		    Z3_ast p2_i0 = mk_int(ctx, 0);

		    /**
		     * initial condition for the model
		     * store [1,1][2,2][3,3] to p1's array
		     */
		    //declare tokens for initial marking

			//declare tok_default_val
			Z3_ast tok0_default = mk_var(ctx, "tok_default", p1_placetype_sort);
			Z3_ast tok1_default = mk_tuple_update(ctx, tok0_default, 0, default_val);
			Z3_ast tok_default_val = mk_tuple_update(ctx, tok1_default, 1, default_val);

		    //store tok1 [1,1]
		    Z3_ast tok1 = mk_var(ctx, "tok1", p1_placetype_sort);
		    Z3_ast tok1_1 = mk_tuple_update(ctx, tok1, 0, one);
		    Z3_ast tok1_2 = mk_tuple_update(ctx, tok1_1, 1, one);//update tok1 to [1,1]
//			Z3_ast s1_0 = mk_var(ctx, "p1", p1_array_sort);
//			Z3_ast s1_i0 = mk_var(ctx, "s1_counter", int_sort);
//			Z3_ast s1_i0_eq = Z3_mk_eq(ctx, s1_i0, zero);
//		    Z3_ast s1_1 = Z3_mk_store(ctx, s1_0, s1_i0, tok1_2);//store tok1 to p1
//		    Z3_ast s1_i1 = mk_add(ctx, s1_i0, one);

		    //store tok2 [2,2]
		    Z3_ast tok2 = mk_var(ctx, "tok2", p1_placetype_sort);
   		    Z3_ast tok2_1 = mk_tuple_update(ctx, tok2, 0, two);
   		    Z3_ast tok2_2 = mk_tuple_update(ctx, tok2_1, 1, two);//update tok2 to [2,2]
//   		    Z3_ast s1_2 = Z3_mk_store(ctx, s1_1, s1_i1, tok2_2);//store tok1 to p1
//   		    Z3_ast s1_i2 = mk_add(ctx, s1_i1, one);

   		    //store tok2 [3,3]
   		    Z3_ast tok3 = mk_var(ctx, "tok3", p1_placetype_sort);
   		    Z3_ast tok3_1 = mk_tuple_update(ctx, tok3, 0, three);
   		    Z3_ast tok3_2 = mk_tuple_update(ctx, tok3_1, 1, three);//update tok3 to [3,3]
//   		    Z3_ast s1_3 = Z3_mk_store(ctx, s1_2, s1_i2, tok3_2);//store tok1 to p1
//   		    Z3_ast s1_i3 = mk_add(ctx, s1_i2, one);

   		 //initial condition
   		    Z3_ast p1_0 = mk_var(ctx, "p1_0", p1_array_sort);
   		    Z3_assert_cnstr(ctx, Z3_mk_eq(ctx, Z3_mk_select(ctx, p1_0, zero), tok1_2));
   		    Z3_assert_cnstr(ctx, Z3_mk_eq(ctx, Z3_mk_select(ctx, p1_0, one), tok2_2));
   		    Z3_assert_cnstr(ctx, Z3_mk_eq(ctx, Z3_mk_select(ctx, p1_0, two), tok3_2));

   		 	Z3_ast p1_i0 = mk_var(ctx, "p1_i0_counter", int_sort);
   		    Z3_assert_cnstr(ctx, Z3_mk_eq(ctx, p1_i0, three));

   		    /**
   		     * transition with quantifier
   		     */
   		    //bound var i
   		    Z3_ast i = Z3_mk_bound(ctx, 0, int_sort);
   		    Z3_ast bound_left = Z3_mk_ge(ctx, i, zero);
   		    Z3_ast bound_right = Z3_mk_le(ctx, i, mk_sub(ctx, p1_i0, one));
   		    Z3_ast bound_i = mk_and(ctx, bound_left, bound_right);//assertion!!!
   		    //"tokx = select(A, i)"
//   		    Z3_ast tok_x = mk_var(ctx, "tok_var", p1_placetype_sort);
   		    Z3_ast tok_x = Z3_mk_select(ctx, p1_0, i);
   		    //transition pre-condition "x.field1
   		    Z3_ast geq_three = Z3_mk_ge(ctx, mk_unary_app(ctx, p1_field0_decl, tok_x), three);//assertion!!!

   		    //update place 2 by add new token
   		    Z3_ast update_val = mk_add(ctx, mk_unary_app(ctx, p1_field0_decl, tok_x), one);
   		    Z3_ast tok_x1 = mk_tuple_update(ctx, tok_x, 0, update_val);//TODO: tok_x1 should be renamed
   		    Z3_ast p2_1 = mk_var(ctx, "p2_1", p2_array_sort);
   		    Z3_ast p2_store = Z3_mk_store(ctx, p2_0, p2_i0, tok_x1);//store
   		    Z3_ast p2_store_eq = Z3_mk_eq(ctx, p2_1, p2_store);
   		    //p2's counter +1
   		    Z3_ast p2_i1 = mk_var(ctx, "p2_i1_counter", int_sort);
   		    Z3_ast p2_counter = Z3_mk_eq(ctx, p2_i1, mk_add(ctx, p2_i0, one));
   		    //update place 1 by remove the fired token
   		    Z3_ast p1_1 = mk_var(ctx, "p1_1", p1_array_sort);
   		    Z3_ast p1_store = Z3_mk_store(ctx, p1_0, i, tok_default_val);
   		    Z3_ast p1_store_eq = Z3_mk_eq(ctx, p1_1, p1_store);
   		    //p1 counter minus 1
   		    Z3_ast p1_i1 = mk_var(ctx, "p1_i1_counter", int_sort);
   		    Z3_ast p1_counter = Z3_mk_eq(ctx, p1_i1, mk_sub(ctx, p1_i0, one));
   		    //copy paste token from p1 index larger than i
//   		    int* index = (int *)malloc(sizeof(int))
//   		   Z3_bool z3b = Z3_get_numeral_int(ctx, i, *index);
//   		   if(z3b == Z3_TRUE) printf("@@@@@@@index i = %d", *index);

   		    Z3_ast axiomTree[6] = {bound_i, geq_three, p1_store_eq, p2_store_eq, p2_counter, p1_counter};
   		    Z3_ast transition_cond = Z3_mk_and(ctx, 6, axiomTree);

   		    //somename
   		    Z3_symbol someName = Z3_mk_int_symbol(ctx, 0);

   		    Z3_ast transition1 = Z3_mk_exists(ctx, 0, 0, 0, 1, &int_sort, &someName, transition_cond);
   		    Z3_assert_cnstr(ctx, transition1);



   		    //error condition "p2 = 4"
   		    //p2.field0
   		    Z3_ast p2_f0 = mk_unary_app(ctx, p1_field0_decl, Z3_mk_select(ctx, p2_1, p2_i0));
   		    Z3_ast error = Z3_mk_eq(ctx, p2_f0, four);
   		    Z3_assert_cnstr(ctx, error);

		    //finish
		    printf("\nFINISH testing ARRAY model...\n");
}

void new_model_Feb1st(Z3_context ctx){
	LOG_MSG("Testing Feb1st model...");
	printf("\n testing Feb1st model");


	//sort declaration
	Z3_sort int_sort = Z3_mk_int_sort(ctx);

	/**
	 * declarations
	 */
	Z3_ast default_val = Z3_mk_int(ctx, -1, int_sort);
				Z3_ast zero = Z3_mk_int(ctx, 0, int_sort);
				Z3_ast one = Z3_mk_int(ctx, 1, int_sort);
				Z3_ast two = Z3_mk_int(ctx, 2, int_sort);
	/**
	 * build a tuple sort
	 */
	Z3_symbol mk_state_name = Z3_mk_string_symbol(ctx, "mk_state");
	Z3_symbol field_names[2] = {
			Z3_mk_string_symbol(ctx, "P1"),
			Z3_mk_string_symbol(ctx, "P2"),
	};
	Z3_sort field_sorts[2] = {
			int_sort, int_sort
	};
	Z3_func_decl mk_state;
	Z3_func_decl field_selects[2] = {0,0};
	Z3_sort state = Z3_mk_tuple_sort(ctx, mk_state_name, 2, field_names, field_sorts, &mk_state, field_selects);
	Z3_func_decl P1 = field_selects[0];
	Z3_func_decl P2 = field_selects[1];

	/**
	 * build an array sort (int => array) for state sequence
	 */
	Z3_sort states_array_sort = Z3_mk_array_sort(ctx, int_sort, state);

	/**
	 * initial condition (marking)
	 */
	Z3_ast state0 = mk_var(ctx, "state0", state);
	Z3_ast paths_array= mk_var(ctx, "state_seq_path", states_array_sort);
	Z3_ast state0_1 = mk_tuple_update(ctx, state0, 0, one);
	Z3_ast state0_2 = mk_tuple_update(ctx, state0_1, 1, default_val);
	Z3_ast i = mk_var(ctx, "current_index", int_sort);
	Z3_assert_cnstr(ctx, Z3_mk_eq(ctx, i, zero));
	Z3_ast paths_array0 = Z3_mk_store(ctx, paths_array, i, state0_2);

	/**
	 * define transitions recursively
	 */

}

void list_framework_Feb1st(Z3_context ctx)
{
    //declaration for building state tuple
    Z3_sort int_sort;
    Z3_sort places_sort;
    Z3_symbol mk_tuple_name;
    Z3_symbol proj_names[3];
    Z3_sort proj_sorts[3];
    Z3_func_decl  mk_tuple_decl;
    Z3_func_decl  proj_decls[3];
    Z3_func_decl get_place0_decl, get_place1_decl, get_place2_decl;

    Z3_ast zero  = mk_int(ctx, 0);
	Z3_ast one = mk_int(ctx, 1);
	Z3_ast two = mk_int(ctx, 2);
	Z3_ast ten  = mk_int(ctx, 10);

    //declaration for building list datatype
    Z3_func_decl nil_decl, is_nil_decl, cons_decl, is_cons_decl, head_decl, tail_decl;

    LOG_MSG("build a list_framework");
	printf("\nbuild a list_framework: Feb 1st model\n");

	//build a state tuple as a sort


			mk_tuple_name = Z3_mk_string_symbol(ctx, "mk_places");

			proj_names[0] = Z3_mk_string_symbol(ctx, "place0");
			proj_names[1] = Z3_mk_string_symbol(ctx, "place1");
			proj_names[2] = Z3_mk_string_symbol(ctx, "place2");

			int_sort = Z3_mk_int_sort(ctx);
			proj_sorts[0] = int_sort;
			proj_sorts[1] = int_sort;
			proj_sorts[2] = int_sort;

			places_sort = Z3_mk_tuple_sort(ctx, mk_tuple_name, 3, proj_names, proj_sorts, &mk_tuple_decl, proj_decls);
			get_place0_decl = proj_decls[0];
			get_place1_decl = proj_decls[1];
			get_place2_decl = proj_decls[2];

	//build a list with state as an list element
			Z3_sort pn_list = Z3_mk_list_sort(ctx, Z3_mk_string_symbol(ctx, "pn_list"), places_sort,
					&nil_decl, &is_nil_decl, &cons_decl, &is_cons_decl, &head_decl, &tail_decl);

			//declare initial state in a list
//			Z3_ast initial_state = mk_var(ctx, "ini_st", places_sort);
			Z3_ast states = mk_var(ctx, "states", pn_list); //declare a new list "PN_List"
			Z3_ast is_cons_states = mk_unary_app(ctx, is_cons_decl, states); //is cons(states)

			Z3_ast head = mk_unary_app(ctx, head_decl, states);// states list head
			Z3_ast head_place0 = mk_unary_app(ctx, get_place0_decl, head); // PN_List's head-> tuple's 'place0'
			Z3_ast head_place1 = mk_unary_app(ctx, get_place1_decl, head); // PN_List's head-> tuple's 'place1'
			Z3_ast head_place2 = mk_unary_app(ctx, get_place2_decl, head); // PN_List's head-> tuple's 'place2'

			//initial condition
			Z3_ast ini_and[3] = {Z3_mk_eq(ctx, head_place0, zero),
					Z3_mk_eq(ctx, head_place1, zero), Z3_mk_eq(ctx, head_place2, one)};
			Z3_ast initial_condition = Z3_mk_and(ctx, 3, ini_and);

//
//			//assert a value 1 to place2 in initial state
//			Z3_ast assert_p2_val = Z3_mk_eq(ctx, head_place2, one);
//			Z3_assert_cnstr(ctx, assert_p2_val);

			//define check_transition function

						//function symbol "check_tr"
						Z3_symbol check_tr_func_symbol = Z3_mk_string_symbol (ctx, "check_tr");
					    Z3_sort check_tr_arg_sorts[1] = {pn_list};

					    Z3_sort check_tr_return_sort = Z3_mk_bool_sort(ctx);
					    unsigned domain_size = 1;

						Z3_func_decl check_tr =
								Z3_mk_func_decl(ctx, check_tr_func_symbol, domain_size, check_tr_arg_sorts, check_tr_return_sort);

						//forall axiom elements
						Z3_ast x = Z3_mk_bound(ctx, 0, pn_list); // x is list variable in quantifier
						Z3_ast check_tr_x = Z3_mk_app(ctx, check_tr, 1, &x);
						Z3_pattern pattern = Z3_mk_pattern(ctx, 1, &check_tr_x); //pattern
						Z3_symbol someName = Z3_mk_int_symbol(ctx, 0);

						Z3_ast head_x = mk_unary_app(ctx, head_decl, x);// x's head
						Z3_ast head_x_place2 = mk_unary_app(ctx, get_place2_decl, head_x);
						Z3_ast head_gt_zero = Z3_mk_gt(ctx, head_x_place2, zero);
						Z3_ast head_lt_ten = Z3_mk_lt(ctx, head_x_place2, ten);
						Z3_ast toCAnd[2] = {head_gt_zero, head_lt_ten};
						Z3_ast head_and_cond = Z3_mk_and(ctx, 2, toCAnd); //10 > headplace2 > 0

//						Z3_bool ite_bool_cond = head_gt_zero;
						Z3_ast tail_x = mk_unary_app(ctx, tail_decl, x);
						Z3_ast tail_head = mk_unary_app(ctx, head_decl, tail_x);
						Z3_ast tail_x_place2 = mk_unary_app(ctx, get_place2_decl, tail_head);
						Z3_ast toSum[2] = {head_x_place2, one};//head.place2 + 1
						Z3_ast tailhead_plusone = Z3_mk_add(ctx, 2, toSum);

//						Z3_ast tailhead_unchange = Z3_mk_eq(ctx, tail_x_place2, head_x_place2);
						Z3_ast transition_condition = Z3_mk_ite(ctx, head_and_cond,
								Z3_mk_eq(ctx, tail_x_place2, tailhead_plusone),
								Z3_mk_eq(ctx, tail_x_place2, head_x_place2)); //transition condition

						Z3_ast twelve  = mk_int(ctx, 12);
						Z3_ast eleven  = mk_int(ctx, 11);
						Z3_ast nine  = mk_int(ctx, 9);
						Z3_ast eight  = mk_int(ctx, 8);

						Z3_ast error_condition_eq_eight = Z3_mk_eq(ctx, tail_x_place2, eight); //error property ite's condition
//						Z3_ast error_condition_tail_lt_ten = Z3_mk_lt(ctx, tail_x_place2, ten); //error property ite's condition

						Z3_ast tail_tail_lst = mk_unary_app(ctx, tail_decl, tail_x);
						Z3_ast is_nil_tail = mk_unary_app(ctx, is_nil_decl, tail_tail_lst);
						Z3_ast is_cons_tail = mk_unary_app(ctx, is_cons_decl, tail_tail_lst);
						Z3_ast property_axiom =
								Z3_mk_ite(ctx, error_condition_eq_eight, is_nil_tail, is_cons_tail);//property axiom
						Z3_ast check_tr_tail_list = mk_unary_app(ctx, check_tr, tail_x); //check_tr(tail(lst));

						Z3_ast is_cons_lst = mk_unary_app(ctx, is_cons_decl, x); //is_cons(lst)
						Z3_ast is_cons_tail_lst = mk_unary_app(ctx, is_cons_decl, tail_x); //is_cons(tail(lst))
						Z3_ast toCondAnd[2] = {is_cons_lst, is_cons_tail_lst};
						Z3_ast axiomTree_cond = Z3_mk_and(ctx, 2, toCondAnd); //(is cons(lst) ^ is cons(tail(lst)))
						Z3_ast toBigAnd[3] = {transition_condition, check_tr_tail_list, property_axiom};
						Z3_ast axiomTree_true = Z3_mk_and(ctx, 3, toBigAnd);
						Z3_ast axiomTree_false = Z3_mk_true(ctx);

						Z3_ast axiomTree =
								Z3_mk_ite(ctx, axiomTree_cond, axiomTree_true, axiomTree_false);//the big if body in forall axiom

						Z3_ast check_tr_forall_axiom =
								Z3_mk_quantifier(ctx, Z3_TRUE, 0, 1, &pattern, 1, &pn_list, &someName, axiomTree);//the body of check_tr

						Z3_assert_cnstr(ctx, check_tr_forall_axiom);
						Z3_ast check_tr_states = mk_unary_app(ctx, check_tr, states);
			//logic context assert
			Z3_ast assertAnd[3] = {is_cons_states, initial_condition, check_tr_states};
			Z3_ast assertCtx = Z3_mk_and(ctx, 3, assertAnd);
			Z3_assert_cnstr(ctx, assertCtx);
}

/**
 * Simple version of list_framework_Feb2nd()
 */
void list_framework_Feb5th(Z3_context ctx){
		Z3_ast zero  = mk_int(ctx, 0);
		Z3_ast one = mk_int(ctx, 1);
		Z3_ast two = mk_int(ctx, 2);
		Z3_ast five = mk_int(ctx, 5);
		Z3_ast ten  = mk_int(ctx, 10);
		Z3_ast twelve  = mk_int(ctx, 12);
		Z3_ast eleven  = mk_int(ctx, 11);
		Z3_ast nine  = mk_int(ctx, 9);
		Z3_ast eight  = mk_int(ctx, 8);
		Z3_sort int_sort = Z3_mk_int_sort(ctx);

		LOG_MSG("build a list_framework");
		printf("\nbuild a list_framework: Feb 5th model\n");

		Z3_ast flag = mk_var(ctx, "flag", int_sort);
		//declaration for building list datatype
		    Z3_func_decl nil_decl, is_nil_decl, cons_decl, is_cons_decl, head_decl, tail_decl;

		    Z3_sort pn_list = Z3_mk_list_sort(ctx, Z3_mk_string_symbol(ctx, "StateList"), int_sort,
		    					&nil_decl, &is_nil_decl, &cons_decl, &is_cons_decl, &head_decl, &tail_decl);

		    Z3_ast states = mk_var(ctx, "states", pn_list); //declare a new list "PN_List"
		    //define check_tr(statelist -> bool) function
		    Z3_symbol check_tr_func_symbol = Z3_mk_string_symbol (ctx, "check_tr");
//		    Z3_sort check_tr_arg_sorts[1] = {pn_list};
		    Z3_sort check_tr_return_sort = Z3_mk_bool_sort(ctx);
		    unsigned domain_size = 1;
		    Z3_func_decl check_tr =
		    		Z3_mk_func_decl(ctx, check_tr_func_symbol, domain_size, &pn_list, check_tr_return_sort);

		    //define forall axiom
		    Z3_ast x = Z3_mk_bound(ctx, 0, pn_list); // x is list variable in quantifier
		    Z3_ast check_tr_x = mk_unary_app(ctx, check_tr, x);
		    Z3_pattern pattern = Z3_mk_pattern(ctx, 1, &check_tr_x); //pattern
		    Z3_symbol someName = Z3_mk_string_symbol(ctx, "lst");

		    Z3_ast head_x = mk_unary_app(ctx, head_decl, x);// x's head
		    Z3_ast head_gt_zero = Z3_mk_gt(ctx, head_x, zero);//head > 0
		    Z3_ast tail_x = mk_unary_app(ctx, tail_decl, x);
		    Z3_ast tail_head = mk_unary_app(ctx, head_decl, tail_x);
		    Z3_ast head_plusone = mk_add(ctx, head_x, one);
//		    Z3_ast transition_condition = Z3_mk_ite(ctx, head_gt_zero,
//		    			Z3_mk_eq(ctx, tail_head, head_plusone),
//		    			Z3_mk_eq(ctx, tail_head, head_x)); //transition condition
		    Z3_ast transition_condition = Z3_mk_eq(ctx, tail_head, head_x);
		    Z3_ast check_tr_tail_list = mk_unary_app(ctx, check_tr, tail_x); //check_tr(tail(lst));

		    Z3_ast error_condition = Z3_mk_eq(ctx, tail_head, eight); //error property ite's condition
//		    Z3_ast error_condition = Z3_mk_false(ctx);
		    Z3_ast tail_tail_lst = mk_unary_app(ctx, tail_decl, tail_x);
		    Z3_ast is_nil_tail = mk_unary_app(ctx, is_nil_decl, tail_tail_lst);
		    Z3_ast is_cons_tail = mk_unary_app(ctx, is_cons_decl, tail_tail_lst);
//		    Z3_ast property_axiom =
//		    			Z3_mk_ite(ctx, error_condition, is_nil_tail, is_cons_tail);//property axiom
		    Z3_ast property_axiom = error_condition;

		    Z3_ast is_cons_lst = mk_unary_app(ctx, is_cons_decl, x); //is_cons(lst)
		    Z3_ast is_cons_tail_lst = mk_unary_app(ctx, is_cons_decl, tail_x); //is_cons(tail(lst))
		    Z3_ast toCondAnd[2] = {is_cons_lst, is_cons_tail_lst};
		    Z3_ast axiomTree_cond = Z3_mk_and(ctx, 2, toCondAnd); //(is cons(lst) ^ is cons(tail(lst)))
		    Z3_ast toBigAnd[3] = {transition_condition, check_tr_tail_list, property_axiom};
			Z3_ast axiomTree_true = Z3_mk_and(ctx, 3, toBigAnd);
			Z3_ast axiomTree_false = Z3_mk_eq(ctx, flag, one);

			Z3_ast axiomTree =
						Z3_mk_ite(ctx, axiomTree_cond, axiomTree_true, axiomTree_false);//the big if body in forall axiom

			Z3_ast check_tr_forall_axiom =
						Z3_mk_forall(ctx, 0, 1, &pattern, 1, &pn_list, &someName, axiomTree);//the body of check_tr

			Z3_assert_cnstr(ctx, check_tr_forall_axiom);

			//is_cons(states)
			Z3_ast is_cons_states = mk_unary_app(ctx, is_cons_decl, states);
			//initial condition
			Z3_ast head_states = mk_unary_app(ctx, head_decl, states);
			Z3_ast initial_condition = Z3_mk_eq(ctx, head_states, one); // head = 1
			//check_tr(states)
			Z3_ast check_tr_states = mk_unary_app(ctx, check_tr, states);

			Z3_ast assertAnd[3] = {is_cons_states, initial_condition, check_tr_states};
			Z3_ast assertCtx = Z3_mk_and(ctx, 3, assertAnd);
			Z3_assert_cnstr(ctx, assertCtx);

	}

void fib(Z3_context ctx){
	LOG_MSG("build a Fib recursive function");
			printf("\nbuild a Fib recursive function\n");
	Z3_sort intSort = Z3_mk_int_sort(ctx);

	/* Some constant integers */
	Z3_ast zero  = Z3_mk_int(ctx, 0, intSort);
	Z3_ast one   = Z3_mk_int(ctx, 1, intSort);
	Z3_ast two   = Z3_mk_int(ctx, 2, intSort);
	Z3_ast three = Z3_mk_int(ctx, 3, intSort);
	Z3_ast four  = Z3_mk_int(ctx, 4, intSort);
	Z3_ast five  = Z3_mk_int(ctx, 5, intSort);
	Z3_ast ten  = Z3_mk_int(ctx, 10, intSort);
	Z3_ast fivefive  = Z3_mk_int(ctx, 55, intSort);



	Z3_func_decl fibonacci = Z3_mk_fresh_func_decl(ctx, "fib", 1, &intSort, intSort);

	/* fib(0) and fib(1) */
	Z3_ast fzero = Z3_mk_app(ctx, fibonacci, 1, &zero);
	Z3_ast fone  = Z3_mk_app(ctx, fibonacci, 1, &one);

	Z3_ast fib0 = Z3_mk_eq(ctx, fzero, zero);
	Z3_ast fib1 = Z3_mk_eq(ctx, fone,  one);

	Z3_ast x = Z3_mk_bound(ctx, 0, intSort);
	Z3_ast fibX = Z3_mk_app(ctx, fibonacci, 1, &x);
	Z3_pattern pattern = Z3_mk_pattern(ctx, 1, &fibX);

	Z3_symbol someName = Z3_mk_int_symbol(ctx, 0);

	/* _ > 1 */
	Z3_ast xGTone = Z3_mk_gt(ctx, x, one);
	Z3_ast xOne[2] = { x, one };
	Z3_ast xTwo[2] = { x, two };
	/* _ - 1 */
	Z3_ast fibXminusOne = Z3_mk_sub(ctx, 2, xOne);
	/* _ - 2 */
	Z3_ast fibXminusTwo = Z3_mk_sub(ctx, 2, xTwo);
	Z3_ast toSum[2] = { Z3_mk_app(ctx, fibonacci, 1, &fibXminusOne), Z3_mk_app(ctx, fibonacci, 1, &fibXminusTwo) };
	/* f(_ - 1) + f(_ - 2) */
	Z3_ast fibSum = Z3_mk_add(ctx, 2, toSum);

	Z3_ast axiomTree = Z3_mk_implies(ctx, xGTone, Z3_mk_eq(ctx, fibX, fibSum));
	Z3_ast fibN = Z3_mk_quantifier(ctx, Z3_TRUE, 0, 1, &pattern, 1, &intSort, &someName, axiomTree);

	Z3_ast fibfour = Z3_mk_app(ctx, fibonacci, 1, &ten);
	Z3_ast fib10 = Z3_mk_eq(ctx, fibfour, five);

	Z3_assert_cnstr(ctx, fib0);
	Z3_assert_cnstr(ctx, fib1);
	Z3_assert_cnstr(ctx, fibN);
	Z3_assert_cnstr(ctx, fib10);

}
/**
 * idea using quantified array
 */
void Feb6th_ArrayFramework(Z3_context ctx){
	LOG_MSG("build a Feb6th_ArrayFramework");
				printf("\nFeb6th_ArrayFramework\n");
		Z3_sort int_sort = Z3_mk_int_sort(ctx);
		/* Some constant integers */
			Z3_ast zero  = Z3_mk_int(ctx, 0, int_sort);
			Z3_ast one   = Z3_mk_int(ctx, 1, int_sort);
			Z3_ast two   = Z3_mk_int(ctx, 2, int_sort);
			Z3_ast three = Z3_mk_int(ctx, 3, int_sort);
			Z3_ast four  = Z3_mk_int(ctx, 4, int_sort);
			Z3_ast five  = Z3_mk_int(ctx, 5, int_sort);
			Z3_ast six  = Z3_mk_int(ctx, 6, int_sort);
			Z3_ast ten  = Z3_mk_int(ctx, 10, int_sort);


			//declare a state sort
			Z3_sort state_sort = Z3_mk_int_sort(ctx);
			//declare state and state'
			Z3_ast cur_st = mk_var(ctx, "cur_state", state_sort);
			Z3_ast next_st = mk_var(ctx, "next_state", state_sort);
			//declare an array sort
			Z3_sort states_array_sort = Z3_mk_array_sort(ctx, int_sort, state_sort);

			//declare an array to store state paths
			Z3_ast StatesSeq = mk_var(ctx, "StatesSeq", states_array_sort);
			//initial condition A[0] = 2
			Z3_assert_cnstr(ctx, Z3_mk_eq(ctx, Z3_mk_select(ctx, StatesSeq, zero), one));
			//define axiom for the transition system
			Z3_ast i = Z3_mk_bound(ctx, 0, int_sort);
			Z3_symbol index_i_name = Z3_mk_string_symbol(ctx, "i");
			//missing pattern........
			//bound i
			Z3_ast bound_left = Z3_mk_ge(ctx, i, zero);
			Z3_ast bound_right = Z3_mk_le(ctx, i, ten);
			Z3_ast bound_i = mk_and(ctx, bound_left, bound_right);//assertion!!!

			/**
			 * define conditions in forall axiom
			 */
			//get current state from states array, select(StatesSeq, i) == current state
			Z3_ast get_cur_st = Z3_mk_eq(ctx, cur_st, Z3_mk_select(ctx, StatesSeq, i));
			//outside if condition: if(cur_state != 0)
			Z3_ast outer_cond = Z3_mk_eq(ctx, cur_st, zero);

			//transition pre-condition: cur_st > 0
			Z3_ast pre_cond = Z3_mk_lt(ctx, cur_st, ten);
			//transition post-condition: next_st = cur_st +1
			Z3_ast post_cond = Z3_mk_eq(ctx, next_st, mk_add(ctx, cur_st, one)); //TODO: cur_st may not match the sort of one
			//Transition Condition
			Z3_ast Trans_cond = Z3_mk_ite(ctx, pre_cond,
												post_cond,
												Z3_mk_eq(ctx, next_st, cur_st));

			//error condition: next_st = 5
			Z3_ast if_error_cond = Z3_mk_eq(ctx, next_st, four);
			//the if in error condition, decide which value stored in next state in State array,
			//if error meet, store 0, if not store next state
			Z3_ast Error_cond = Z3_mk_ite(ctx, if_error_cond,
												Z3_mk_eq(ctx, Z3_mk_select(ctx, StatesSeq, mk_add(ctx, i, one)), zero),
												Z3_mk_eq(ctx, Z3_mk_select(ctx, StatesSeq, mk_add(ctx, i, one)), next_st));
			//big if model body
			Z3_ast bigif = Z3_mk_ite(ctx, outer_cond,
										Z3_mk_eq(ctx, Z3_mk_select(ctx, StatesSeq, mk_add(ctx, i, one)), zero),
										mk_and(ctx, Trans_cond, Error_cond)
										);
			Z3_ast body_and[2] = {get_cur_st, bigif};
			Z3_ast model_body = Z3_mk_and(ctx, 2, body_and);

			//big imply from bound i
			Z3_ast bigImply = Z3_mk_implies(ctx, bound_i, model_body);

			//for all axiom
			Z3_ast model_axiom = Z3_mk_forall(ctx, 0, 0, 0, 1, &int_sort, &index_i_name, bigImply);
			Z3_assert_cnstr(ctx, model_axiom);

}
/**
 * take error condition out of the forall axiom tree, and use exist quantifier to represent property formula
 * This one works!!!
 */

void Second_Feb6th_ArrayFramework(Z3_context ctx){
	LOG_MSG("build a Feb6th_ArrayFramework");
				printf("\nSecond Feb6th_ArrayFramework\n");
		Z3_sort int_sort = Z3_mk_int_sort(ctx);
		Z3_sort bool_sort = Z3_mk_bool_sort(ctx);
		/* Some constant integers */
		Z3_ast minusone  = Z3_mk_int(ctx, -1, int_sort);
			Z3_ast zero  = Z3_mk_int(ctx, 0, int_sort);
			Z3_ast one   = Z3_mk_int(ctx, 1, int_sort);
			Z3_ast two   = Z3_mk_int(ctx, 2, int_sort);
			Z3_ast three = Z3_mk_int(ctx, 3, int_sort);
			Z3_ast four  = Z3_mk_int(ctx, 4, int_sort);
			Z3_ast five  = Z3_mk_int(ctx, 5, int_sort);
			Z3_ast six  = Z3_mk_int(ctx, 6, int_sort);
			Z3_ast eight  = Z3_mk_int(ctx, 6, int_sort);

			Z3_ast ten  = Z3_mk_int(ctx, 10, int_sort);
			Z3_ast minus10  = Z3_mk_int(ctx, -10, int_sort);
			Z3_ast eleven  = Z3_mk_int(ctx, 11, int_sort);
			Z3_ast fifteen  = Z3_mk_int(ctx, 15, int_sort);
			Z3_ast minus5  = Z3_mk_int(ctx, -5, int_sort);
			Z3_ast minus15  = Z3_mk_int(ctx, -15, int_sort);
			Z3_ast minus20  = Z3_mk_int(ctx, -20, int_sort);

			Z3_ast flag = mk_var(ctx, "flag", bool_sort);
			//declare a state sort
			Z3_sort state_sort = Z3_mk_int_sort(ctx);
			//declare an array sort
			Z3_sort states_array_sort = Z3_mk_array_sort(ctx, int_sort, int_sort);

			//declare an array to store state paths
			Z3_ast StatesSeq = mk_var(ctx, "StatesSeq", states_array_sort);
			//initial condition
			Z3_assert_cnstr(ctx, Z3_mk_eq(ctx, Z3_mk_select(ctx, StatesSeq, zero), one));


			//define axiom for the transition system
			Z3_ast i = Z3_mk_bound(ctx, 0, int_sort);
			Z3_symbol forall_index_i_name = Z3_mk_string_symbol(ctx, "i");
			Z3_ast bound_left = Z3_mk_ge(ctx, i, zero);
			Z3_ast bound_right = Z3_mk_le(ctx, i, ten);
			Z3_ast bound_i = mk_and(ctx, bound_left, bound_right);
			/**
			 * define conditions in forall axiom
			 */
			//get current state from states array, select(StatesSeq, i) == current state
//			Z3_ast get_cur_st = Z3_mk_eq(ctx, cur_st, Z3_mk_select(ctx, StatesSeq, i));

			//transition pre-condition: cur_st > 0
//			Z3_ast pre_cond = Z3_mk_gt(ctx, cur_st, zero);
			//transition post-condition: next_st = cur_st +1
//			Z3_ast post_cond = Z3_mk_eq(ctx, next_st, mk_add(ctx, Z3_mk_select(ctx, StatesSeq, i), one)); //TODO: cur_st may not match the sort of one
			//Transition Condition
//			Z3_ast Trans_cond = Z3_mk_ite(ctx, pre_cond,
//												post_cond,
//												Z3_mk_eq(ctx, next_st, cur_st));
			//try plus one or minus one
			Z3_ast transition_incre_one = Z3_mk_eq(ctx, Z3_mk_select(ctx, StatesSeq, mk_add(ctx, i, one)),
					mk_add(ctx, Z3_mk_select(ctx, StatesSeq, i), one));
			Z3_ast transition_decre_one = Z3_mk_eq(ctx, Z3_mk_select(ctx, StatesSeq, mk_add(ctx, i, one)),
								mk_sub(ctx, Z3_mk_select(ctx, StatesSeq, i), one));
			Z3_ast transition_relation = mk_or(ctx, transition_incre_one, transition_decre_one);
			Z3_ast bigif = Z3_mk_ite(ctx, Z3_mk_gt(ctx, Z3_mk_select(ctx, StatesSeq, i), minus20),
													transition_relation,
													Z3_mk_eq(ctx, Z3_mk_select(ctx, StatesSeq, mk_add(ctx, i, one)),
															Z3_mk_select(ctx, StatesSeq, i))
													);

//			Z3_ast if_error = Z3_mk_ite(ctx, Z3_mk_eq(ctx, Z3_mk_select(ctx, StatesSeq, mk_add(ctx, i, one)), minusone),
//											Z3_mk_eq(ctx, flag, Z3_mk_true(ctx)),
//											Z3_mk_eq(ctx, flag, Z3_mk_false(ctx)));
//			Z3_ast bigif_and_iferror = mk_and(ctx, bigif, if_error);
			Z3_ast imply = Z3_mk_implies(ctx, bound_i, bigif);

			//for all axiom
			Z3_ast model_axiom = Z3_mk_forall(ctx, 0, 0, 0, 1, &int_sort, &forall_index_i_name, imply);
			Z3_assert_cnstr(ctx, model_axiom);
//			Z3_assert_cnstr(ctx, flag);

			/**
			 * using exist detect all array to see if it violates property
			 */
			Z3_ast ei = Z3_mk_bound(ctx, 0, int_sort);
			Z3_symbol exist_index_i_name = Z3_mk_string_symbol(ctx, "ei");

			Z3_ast Error_cond = Z3_mk_eq(ctx, Z3_mk_select(ctx, StatesSeq, ei), minus5);
			Z3_ast ei_left = Z3_mk_ge(ctx, ei, zero);
			Z3_ast ei_right = Z3_mk_le(ctx, ei, ten);
			Z3_ast ei_bound = mk_and(ctx, ei_left, ei_right);

			Z3_ast ei_and = mk_and(ctx, ei_bound, Error_cond);
			Z3_ast property_axiom = Z3_mk_exists(ctx, 0, 0, 0, 1, &int_sort, &exist_index_i_name, ei_and);
			Z3_assert_cnstr(ctx, property_axiom);


}
int main() {
#ifdef LOG_Z3_CALLS
    Z3_open_log("z3.log");
#endif
//    array_example3();
//    Z3_config cfg = Z3_mk_config();
//    Z3_set_param_value(cfg, "MODEL", "true");
    		Z3_config  cfg;
        	Z3_context ctx;
         	cfg = Z3_mk_config();
           Z3_set_param_value(cfg, "MODEL", "true");
           ctx = mk_context_custom(cfg, error_handler);

           list_framework_Feb5th(ctx);
//           fib(ctx);
    //check context satisfaction
    check(ctx, Z3_L_TRUE);

    printf("\nCONTEXT:\n%s\nEND OF CONTEXT\n", Z3_context_to_string(ctx));
    /* delete logical context */
     Z3_del_context(ctx);
     Z3_del_config(cfg);
    return 0;
}
