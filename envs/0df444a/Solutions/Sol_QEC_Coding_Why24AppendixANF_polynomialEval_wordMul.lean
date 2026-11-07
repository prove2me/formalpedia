-- Prove2me | solution 1 for QEC.Coding.Why24AppendixANF.polynomialEval_wordMul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:40:11.491024+00:00
-- url     : https://prove2.me/submissions/a32d27da-d802-4b7c-85fc-aea51566653f

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_SupportCertificate
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Field
import Theorems.Thm_QEC_Coding_Why24AppendixANF_alphaReduction_eval
import Theorems.Thm_QEC_Coding_Why24AppendixANF_wordMul_eq_sum
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
open scoped Matrix
namespace QEC.Coding.Why24AppendixANF
theorem _root_.solution (left right : Word) :
    polynomialEval (wordMul left right) =
      polynomialEval left * polynomialEval right := by
  calc
    polynomialEval (wordMul left right) =
        ∑ first : Fin 10, ∑ second : Fin 10,
          (left first * right second) •
            f1024Alpha ^ ((first : Nat) + (second : Nat)) := by
              rw [wordMul_eq_sum]
              simp only [map_sum, map_smul, alphaReduction_eval]
    _ = (∑ first : Fin 10, left first • f1024Alpha ^ (first : Nat)) *
          ∑ second : Fin 10, right second • f1024Alpha ^ (second : Nat) := by
            rw [Fintype.sum_mul_sum]
            apply Finset.sum_congr rfl
            intro first _
            apply Finset.sum_congr rfl
            intro second _
            simp only [Algebra.smul_def, map_mul]
            rw [pow_add]
            ring
    _ = polynomialEval left * polynomialEval right := rfl
end QEC.Coding.Why24AppendixANF
