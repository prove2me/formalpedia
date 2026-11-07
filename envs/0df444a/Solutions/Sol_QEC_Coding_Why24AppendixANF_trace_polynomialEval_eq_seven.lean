-- Prove2me | solution 1 for QEC.Coding.Why24AppendixANF.trace_polynomialEval_eq_seven
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:36:31.764036+00:00
-- url     : https://prove2.me/submissions/52dee1f5-a652-40a4-b441-a1a2444fca26

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Field
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Evaluation
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_Why24BooleanANF_evaluate_generator
import Theorems.Thm_QEC_Coding_Why24BooleanANF_generator_mul_self
import Theorems.Thm_QEC_Coding_f1024PolynomialBasis_apply
import Theorems.Thm_QEC_Coding_f1024PolynomialTraceMatrix_eq
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


section
noncomputable section
namespace QEC.Coding.Why24AppendixANF
open scoped BigOperators
open Why24BooleanANF
private theorem trace_alpha_pow (power : Fin 10) :
    Algebra.trace (ZMod 2) F1024 (f1024Alpha ^ (power : Nat)) =
      f1024PolynomialTraceGram power 0 := by
  have hentry := congr_fun (congr_fun f1024PolynomialTraceMatrix_eq power) 0
  simpa [Algebra.traceMatrix_apply, Algebra.traceForm_apply,
    f1024PolynomialBasis_apply] using hentry
end QEC.Coding.Why24AppendixANF
end
end

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
open scoped BigOperators
open Why24BooleanANF
namespace QEC.Coding.Why24AppendixANF
theorem _root_.solution (coordinates : Word) :
    Algebra.trace (ZMod 2) F1024 (polynomialEval coordinates) = coordinates 7 := by
  change
    Algebra.trace (ZMod 2) F1024
        (∑ power : Fin 10, coordinates power • f1024Alpha ^ (power : Nat)) =
      coordinates 7
  rw [map_sum]
  simp_rw [(Algebra.trace (ZMod 2) F1024).map_smul, trace_alpha_pow]
  rw [Fintype.sum_eq_single (7 : Fin 10)]
  · simp [f1024PolynomialTraceGram]
  · intro power hpower
    fin_cases power <;> simp_all [f1024PolynomialTraceGram]
end QEC.Coding.Why24AppendixANF
