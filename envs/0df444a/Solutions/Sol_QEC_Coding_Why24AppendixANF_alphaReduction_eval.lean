-- Prove2me | solution 1 for QEC.Coding.Why24AppendixANF.alphaReduction_eval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:37:48.065179+00:00
-- url     : https://prove2.me/submissions/a8ef56c6-4bdd-4124-992b-1d6a24439d4b

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_SupportCertificate
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Field
import Theorems.Thm_QEC_Coding_Why24AppendixANF_polynomialEval_single
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_Why24BooleanANF_evaluate_generator
import Theorems.Thm_QEC_Coding_Why24BooleanANF_generator_mul_self
import Theorems.Thm_QEC_Coding_f1024Alpha_pow_ten
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
open scoped Matrix
private theorem alpha_pow_ten_add (n : Nat) :
    f1024Alpha ^ (10 + n) = f1024Alpha ^ n + f1024Alpha ^ (3 + n) := by
  calc
    f1024Alpha ^ (10 + n) = f1024Alpha ^ 10 * f1024Alpha ^ n := by
      rw [pow_add]
    _ = (1 + f1024Alpha ^ 3) * f1024Alpha ^ n := by
      rw [f1024Alpha_pow_ten]
    _ = f1024Alpha ^ n + f1024Alpha ^ (3 + n) := by
      rw [pow_add]
      ring
private theorem alphaReduction_eval_0 :
    polynomialEval (alphaReduction 0) = f1024Alpha ^ 0 := by
  have hrow : alphaReduction (0 : Fin 19) = Pi.single (0 : Fin 10) 1 := by decide
  rw [hrow]
  exact polynomialEval_single (0 : Fin 10)
private theorem alphaReduction_eval_1 :
    polynomialEval (alphaReduction 1) = f1024Alpha ^ 1 := by
  have hrow : alphaReduction (1 : Fin 19) = Pi.single (1 : Fin 10) 1 := by decide
  rw [hrow]
  exact polynomialEval_single (1 : Fin 10)
private theorem alphaReduction_eval_2 :
    polynomialEval (alphaReduction 2) = f1024Alpha ^ 2 := by
  have hrow : alphaReduction (2 : Fin 19) = Pi.single (2 : Fin 10) 1 := by decide
  rw [hrow]
  exact polynomialEval_single (2 : Fin 10)
private theorem alphaReduction_eval_3 :
    polynomialEval (alphaReduction 3) = f1024Alpha ^ 3 := by
  have hrow : alphaReduction (3 : Fin 19) = Pi.single (3 : Fin 10) 1 := by decide
  rw [hrow]
  exact polynomialEval_single (3 : Fin 10)
private theorem alphaReduction_eval_4 :
    polynomialEval (alphaReduction 4) = f1024Alpha ^ 4 := by
  have hrow : alphaReduction (4 : Fin 19) = Pi.single (4 : Fin 10) 1 := by decide
  rw [hrow]
  exact polynomialEval_single (4 : Fin 10)
private theorem alphaReduction_eval_5 :
    polynomialEval (alphaReduction 5) = f1024Alpha ^ 5 := by
  have hrow : alphaReduction (5 : Fin 19) = Pi.single (5 : Fin 10) 1 := by decide
  rw [hrow]
  exact polynomialEval_single (5 : Fin 10)
private theorem alphaReduction_eval_6 :
    polynomialEval (alphaReduction 6) = f1024Alpha ^ 6 := by
  have hrow : alphaReduction (6 : Fin 19) = Pi.single (6 : Fin 10) 1 := by decide
  rw [hrow]
  exact polynomialEval_single (6 : Fin 10)
private theorem alphaReduction_eval_7 :
    polynomialEval (alphaReduction 7) = f1024Alpha ^ 7 := by
  have hrow : alphaReduction (7 : Fin 19) = Pi.single (7 : Fin 10) 1 := by decide
  rw [hrow]
  exact polynomialEval_single (7 : Fin 10)
private theorem alphaReduction_eval_8 :
    polynomialEval (alphaReduction 8) = f1024Alpha ^ 8 := by
  have hrow : alphaReduction (8 : Fin 19) = Pi.single (8 : Fin 10) 1 := by decide
  rw [hrow]
  exact polynomialEval_single (8 : Fin 10)
private theorem alphaReduction_eval_9 :
    polynomialEval (alphaReduction 9) = f1024Alpha ^ 9 := by
  have hrow : alphaReduction (9 : Fin 19) = Pi.single (9 : Fin 10) 1 := by decide
  rw [hrow]
  exact polynomialEval_single (9 : Fin 10)
private theorem alphaReduction_eval_10 :
    polynomialEval (alphaReduction 10) = f1024Alpha ^ 10 := by
  have hrow : alphaReduction (10 : Fin 19) =
      Pi.single (0 : Fin 10) 1 + Pi.single (3 : Fin 10) 1 := by decide
  have hpower : f1024Alpha ^ 10 = 1 + f1024Alpha ^ 3 := by
    simpa using alpha_pow_ten_add 0
  simp only [hrow, map_add, polynomialEval_single]
  exact hpower.symm
private theorem alphaReduction_eval_11 :
    polynomialEval (alphaReduction 11) = f1024Alpha ^ 11 := by
  have hrow : alphaReduction (11 : Fin 19) =
      Pi.single (1 : Fin 10) 1 + Pi.single (4 : Fin 10) 1 := by decide
  have hpower : f1024Alpha ^ 11 = f1024Alpha + f1024Alpha ^ 4 := by
    simpa using alpha_pow_ten_add 1
  simpa [hrow, polynomialEval_single] using hpower.symm
private theorem alphaReduction_eval_12 :
    polynomialEval (alphaReduction 12) = f1024Alpha ^ 12 := by
  have hrow : alphaReduction (12 : Fin 19) =
      Pi.single (2 : Fin 10) 1 + Pi.single (5 : Fin 10) 1 := by decide
  have hpower : f1024Alpha ^ 12 = f1024Alpha ^ 2 + f1024Alpha ^ 5 := by
    simpa using alpha_pow_ten_add 2
  simp only [hrow, map_add, polynomialEval_single]
  exact hpower.symm
private theorem alphaReduction_eval_13 :
    polynomialEval (alphaReduction 13) = f1024Alpha ^ 13 := by
  have hrow : alphaReduction (13 : Fin 19) =
      Pi.single (3 : Fin 10) 1 + Pi.single (6 : Fin 10) 1 := by decide
  have hpower : f1024Alpha ^ 13 = f1024Alpha ^ 3 + f1024Alpha ^ 6 := by
    simpa using alpha_pow_ten_add 3
  simp only [hrow, map_add, polynomialEval_single]
  exact hpower.symm
private theorem alphaReduction_eval_14 :
    polynomialEval (alphaReduction 14) = f1024Alpha ^ 14 := by
  have hrow : alphaReduction (14 : Fin 19) =
      Pi.single (4 : Fin 10) 1 + Pi.single (7 : Fin 10) 1 := by decide
  have hpower : f1024Alpha ^ 14 = f1024Alpha ^ 4 + f1024Alpha ^ 7 := by
    simpa using alpha_pow_ten_add 4
  simp only [hrow, map_add, polynomialEval_single]
  exact hpower.symm
private theorem alphaReduction_eval_15 :
    polynomialEval (alphaReduction 15) = f1024Alpha ^ 15 := by
  have hrow : alphaReduction (15 : Fin 19) =
      Pi.single (5 : Fin 10) 1 + Pi.single (8 : Fin 10) 1 := by decide
  have hpower : f1024Alpha ^ 15 = f1024Alpha ^ 5 + f1024Alpha ^ 8 := by
    simpa using alpha_pow_ten_add 5
  simp only [hrow, map_add, polynomialEval_single]
  exact hpower.symm
private theorem alphaReduction_eval_16 :
    polynomialEval (alphaReduction 16) = f1024Alpha ^ 16 := by
  have hrow : alphaReduction (16 : Fin 19) =
      Pi.single (6 : Fin 10) 1 + Pi.single (9 : Fin 10) 1 := by decide
  have hpower : f1024Alpha ^ 16 = f1024Alpha ^ 6 + f1024Alpha ^ 9 := by
    simpa using alpha_pow_ten_add 6
  simp only [hrow, map_add, polynomialEval_single]
  exact hpower.symm
private theorem alphaReduction_eval_17 :
    polynomialEval (alphaReduction 17) = f1024Alpha ^ 17 := by
  have hrow : alphaReduction (17 : Fin 19) =
      Pi.single (0 : Fin 10) 1 + Pi.single (3 : Fin 10) 1 +
        Pi.single (7 : Fin 10) 1 := by decide
  have hpower : f1024Alpha ^ 17 = 1 + f1024Alpha ^ 3 + f1024Alpha ^ 7 := by
    calc
      f1024Alpha ^ 17 = f1024Alpha ^ 7 + f1024Alpha ^ 10 := by
        simpa using alpha_pow_ten_add 7
      _ = 1 + f1024Alpha ^ 3 + f1024Alpha ^ 7 := by
        rw [f1024Alpha_pow_ten]
        ring
  simp only [hrow, map_add, polynomialEval_single]
  exact hpower.symm
private theorem alphaReduction_eval_18 :
    polynomialEval (alphaReduction 18) = f1024Alpha ^ 18 := by
  have hrow : alphaReduction (18 : Fin 19) =
      Pi.single (1 : Fin 10) 1 + Pi.single (4 : Fin 10) 1 +
        Pi.single (8 : Fin 10) 1 := by decide
  have h11 : f1024Alpha ^ 11 = f1024Alpha + f1024Alpha ^ 4 := by
    simpa using alpha_pow_ten_add 1
  have hpower : f1024Alpha ^ 18 =
      f1024Alpha + f1024Alpha ^ 4 + f1024Alpha ^ 8 := by
    calc
      f1024Alpha ^ 18 = f1024Alpha ^ 8 + f1024Alpha ^ 11 := by
        simpa using alpha_pow_ten_add 8
      _ = f1024Alpha + f1024Alpha ^ 4 + f1024Alpha ^ 8 := by
        rw [h11]
        ring
  simpa [hrow, polynomialEval_single] using hpower.symm
end QEC.Coding.Why24AppendixANF
end
end

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
open scoped BigOperators
open scoped Matrix
namespace QEC.Coding.Why24AppendixANF
theorem _root_.solution (power : Fin 19) :
    polynomialEval (alphaReduction power) = f1024Alpha ^ (power : Nat) := by
  fin_cases power
  · exact alphaReduction_eval_0
  · exact alphaReduction_eval_1
  · exact alphaReduction_eval_2
  · exact alphaReduction_eval_3
  · exact alphaReduction_eval_4
  · exact alphaReduction_eval_5
  · exact alphaReduction_eval_6
  · exact alphaReduction_eval_7
  · exact alphaReduction_eval_8
  · exact alphaReduction_eval_9
  · exact alphaReduction_eval_10
  · exact alphaReduction_eval_11
  · exact alphaReduction_eval_12
  · exact alphaReduction_eval_13
  · exact alphaReduction_eval_14
  · exact alphaReduction_eval_15
  · exact alphaReduction_eval_16
  · exact alphaReduction_eval_17
  · exact alphaReduction_eval_18
end QEC.Coding.Why24AppendixANF
