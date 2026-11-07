-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.one_lt_natCard_constantProjectiveClass
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:48:05.093467+00:00
-- url     : https://prove2.me/submissions/5ccb0673-ea0c-41d9-a1bd-74db12cc0ccf

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_Norm
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexSplitting
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexRepresentation
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_BasePrime_one_le
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Rank_two_le_matrixRank
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cartwrightStegerNormUnit_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantUnitMatrix_val
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexConstantGL_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexCyclicGeneratorGL_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_natCard_constantProjectiveClass_mul_baseScalar
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueBGL_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueConstantGL_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueXAdjoinRootEquiv_root
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueYAdjoinRootEquiv_root
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.cartwrightStegerNormUnit_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantUnitMatrix_val
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexConstantGL_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexCyclicGeneratorGL_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueBGL_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueConstantGL_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueXAdjoinRootEquiv_root
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueYAdjoinRootEquiv_root



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) :
    1 < Nat.card (ConstantProjectiveClass P r) := by
  have hcard := natCard_constantProjectiveClass_mul_baseScalar P r
  have hq : 1 ≤ P.q := P.one_le
  have hsub : P.q - 1 + 1 = P.q := Nat.sub_add_cancel hq
  by_contra hnot
  have hc : Nat.card (ConstantProjectiveClass P r) ≤ 1 :=
    Nat.le_of_not_gt hnot
  have hmul :
      Nat.card (ConstantProjectiveClass P r) * (P.q - 1) ≤
        P.q - 1 := by
    simpa using Nat.mul_le_mul_right (P.q - 1) hc
  have hpowSub : P.q ^ r.matrixRank - 1 ≤ P.q - 1 := by
    rw [← hcard]
    exact hmul
  have hpow : P.q ^ r.matrixRank ≤ P.q := by
    calc
      P.q ^ r.matrixRank = P.q ^ r.matrixRank - 1 + 1 :=
        (Nat.sub_add_cancel (one_le_pow₀ hq)).symm
      _ ≤ P.q - 1 + 1 := Nat.add_le_add_right hpowSub 1
      _ = P.q := hsub
  have hlt : P.q < P.q ^ r.matrixRank := by
    simpa using Nat.pow_lt_pow_right
      (lt_of_lt_of_le (by norm_num : 1 < 5) P.five_le)
      (show 1 < r.matrixRank by
        exact lt_of_lt_of_le (by norm_num) (Rank.two_le_matrixRank r))
  exact (Nat.not_lt_of_ge hpow) hlt
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
