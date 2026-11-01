-- Prove2me | solution 1 for TensorNP.Bilinear.theorem_6_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T13:36:03.302225+00:00
-- url     : https://prove2.me/submissions/a056629c-4cb8-4998-b9c6-344abf2ae927
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_TensorNP_Bilinear_Encoding
import Definitions.Def_TensorNP_Bilinear_SingularValue
import Theorems.Thm_TensorNP_Bilinear_theorem_3_7

open CookPvsNP TensorNP.Bilinear

private lemma isL2SingularValue_zero_iff_tbf {I J K F : Type*} [Fintype I] [Fintype J] [Fintype K] [CommRing F]
    (A : I → J → K → F) :
    IsL2SingularValue A 0 ↔ TBF A := by
  simp [IsL2SingularValue, TBF]

private lemma isL3SingularValue_zero_iff_tbf {I J K F : Type*} [Fintype I] [Fintype J] [Fintype K] [CommRing F]
    (A : I → J → K → F) :
    IsL3SingularValue A 0 ↔ TBF A := by
  simp [IsL3SingularValue, TBF]

private lemma zeroL2SingLang_eq_tbfLang (F : Type*) [Field F] :
    zeroL2SingLang F = tbfLang F := by
  ext w
  simp [zeroL2SingLang, tbfLang, isL2SingularValue_zero_iff_tbf]

private lemma zeroL3SingLang_eq_tbfLang (F : Type*) [Field F] :
    zeroL3SingLang F = tbfLang F := by
  ext w
  simp [zeroL3SingLang, tbfLang, isL3SingularValue_zero_iff_tbf]

theorem solution :
    PolyReducible TensorNP.Eigen.threeColLang (zeroL2SingLang ℝ) ∧
    PolyReducible TensorNP.Eigen.threeColLang (zeroL2SingLang ℂ) ∧
    PolyReducible TensorNP.Eigen.threeColLang (zeroL3SingLang ℝ) ∧
    PolyReducible TensorNP.Eigen.threeColLang (zeroL3SingLang ℂ) := by
  rw [zeroL2SingLang_eq_tbfLang ℝ, zeroL2SingLang_eq_tbfLang ℂ,
      zeroL3SingLang_eq_tbfLang ℝ, zeroL3SingLang_eq_tbfLang ℂ]
  exact ⟨theorem_3_7.1, theorem_3_7.2, theorem_3_7.1, theorem_3_7.2⟩
