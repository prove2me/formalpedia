-- Prove2me | solution 1 for QEC.Coding.Why24AppendixANF.generator_mul_generator_mul_generator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:09:57.16876+00:00
-- url     : https://prove2.me/submissions/ade2b58c-a18a-464a-b618-54538806029f

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Quadratic_Certificate
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Certificate
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Symbolic
import Theorems.Thm_QEC_Coding_Why24AppendixANF_generator_mul_generator
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_Why24BooleanANF_evaluate_generator
import Theorems.Thm_QEC_Coding_Why24BooleanANF_generator_mul_self
import Theorems.Thm_QEC_Coding_why24QuditZ_apply
import Theorems.Thm_QEC_Coding_why24U_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.Why24BooleanANF.evaluate_generator
attribute [local simp] QEC.Coding.Why24BooleanANF.generator_mul_self
attribute [local simp] QEC.Coding.why24QuditZ_apply
attribute [local simp] QEC.Coding.why24U_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
attribute [local simp] QEC.Semantics.OperatorMatrix.matrixUnit_apply
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.Qubit.localXSupport_apply
attribute [local simp] QEC.Semantics.Qubit.localZSupport_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator



set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
open scoped BigOperators
open Why24BooleanANF
namespace QEC.Coding.Why24AppendixANF
theorem _root_.solution
    (first second third : Fin 10) :
    generator first * generator second * generator third =
      MonoidAlgebra.single ⟨{first, second, third}⟩ 1 := by
  rw [generator_mul_generator]
  simp only [generator]
  rw [MonoidAlgebra.single_mul_single, one_mul]
  congr 1
  apply Monomial.ext
  simp only [mul_support]
  simp
end QEC.Coding.Why24AppendixANF
