################################################################################
# Automatically-generated file. Do not edit!
################################################################################

# Add inputs and outputs from these tool invocations to the build variables 
C_SRCS += \
../smtList/PNnet.c 

OBJS += \
./smtList/PNnet.o 

C_DEPS += \
./smtList/PNnet.d 


# Each subdirectory must supply rules for building sources it contributes
smtList/%.o: ../smtList/%.c
	@echo 'Building file: $<'
	@echo 'Invoking: Cross GCC Compiler'
	gcc -O3 -Wall -c -fmessage-length=0 -MMD -MP -MF"$(@:%.o=%.d)" -MT"$(@:%.o=%.d)" -o "$@" "$<"
	@echo 'Finished building: $<'
	@echo ' '


