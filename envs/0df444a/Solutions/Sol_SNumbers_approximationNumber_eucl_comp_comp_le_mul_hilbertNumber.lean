-- Prove2me | solution 1 for SNumbers.approximationNumber_eucl_comp_comp_le_mul_hilbertNumber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:20:49.93944+00:00
-- url     : https://prove2.me/submissions/79c9f282-de87-4861-817b-1fd3b6f4c77e

module
public import Definitions.Def_SNumbers_Hilbert
public import Definitions.Def_SNumbers_Uniqueness
public import Definitions.Def_SNumbers_Bernstein
public import Definitions.Def_SNumbers_Gelfand
public import Definitions.Def_SNumbers_Kolmogorov
public import Definitions.Def_SNumbers_SingularValuesFinDim
public import Definitions.Def_BasicResults_GarlingGordon
public import Definitions.Def_BasicResults_KadetsSnobar
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.NormDet
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Definitions.Def_SNumbers_Inequalities
public import Theorems.Thm_SNumbers_approximationNumber_comp_comp_le_mul_hilbertNumber
public import Theorems.Thm_ContinuousLinearMap_rank_zero
public import Theorems.Thm_John_rankOneSA_apply
public import Theorems.Thm_SNumbers_Complexification_adjoint_complexify
public import Theorems.Thm_SNumbers_Complexification_complexify_conj
public import Theorems.Thm_SNumbers_Complexification_complexify_fst
public import Theorems.Thm_SNumbers_Complexification_complexify_ofReal
public import Theorems.Thm_SNumbers_Complexification_complexify_snd
public import Theorems.Thm_SNumbers_Complexification_norm_complexify
public import Theorems.Thm_SNumbers_approximationNumber_comp_comp_le
public import Theorems.Thm_SNumbers_approximationNumber_nonneg
public import Theorems.Thm_SNumbers_approximationNumber_zero_eq_norm
public import Theorems.Thm_SNumbers_bernsteinNumber_zero_eq_norm
public import Theorems.Thm_SNumbers_exists_l2_section
public import Theorems.Thm_SNumbers_hilbertNumber_nonneg
public import Theorems.Thm_Submodule_liftQL_mkQL
attribute [local simp] ContinuousLinearMap.rank_zero
attribute [local simp] John.rankOneSA_apply
attribute [local simp] SNumbers.Complexification.adjoint_complexify
attribute [local simp] SNumbers.Complexification.complexify_conj
attribute [local simp] SNumbers.Complexification.complexify_fst
attribute [local simp] SNumbers.Complexification.complexify_ofReal
attribute [local simp] SNumbers.Complexification.complexify_snd
attribute [local simp] SNumbers.Complexification.norm_complexify
attribute [local simp] SNumbers.approximationNumber_zero_eq_norm
attribute [local simp] SNumbers.bernsteinNumber_zero_eq_norm
attribute [local simp] Submodule.liftQL_mkQL



set_option autoImplicit true
@[expose] public section
public section
universe u
open ContinuousLinearMap
open SNumbers
variable {𝕜 : Type u} [RCLike 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [CompleteSpace X] [CompleteSpace Y]
omit [CompleteSpace X] [CompleteSpace Y]
namespace SNumbers
theorem _root_.solution (S : X →L[𝕜] Y) (n k : ℕ)
    (A' : EuclideanSpace 𝕜 (Fin (n + 1)) →L[𝕜] X)
    (B' : Y →L[𝕜] EuclideanSpace 𝕜 (Fin (n + 1))) :
    approximationNumber (B'.comp (S.comp A')) k ≤ ‖B'‖ * ‖A'‖ * hilbertNumber S k := by
  obtain ⟨jm, pm, hpj, hp1, hj1⟩ := exists_l2_section (𝕜 := 𝕜) n
  have hpj_apply : ∀ z, pm (jm z) = z := fun z => by
    rw [← ContinuousLinearMap.comp_apply, hpj, ContinuousLinearMap.id_apply]
  set AL : L2 𝕜 →L[𝕜] X := A'.comp pm with hAL
  set BL : Y →L[𝕜] L2 𝕜 := jm.comp B' with hBL
  have hMeq : B'.comp (S.comp A') = pm.comp ((BL.comp (S.comp AL)).comp jm) := by
    ext x
    simp only [hAL, hBL, ContinuousLinearMap.comp_apply]
    rw [hpj_apply x, hpj_apply (B' (S (A' x)))]
  have hak : 0 ≤ approximationNumber (BL.comp (S.comp AL)) k := approximationNumber_nonneg _ _
  calc approximationNumber (B'.comp (S.comp A')) k
      = approximationNumber (pm.comp ((BL.comp (S.comp AL)).comp jm)) k := by rw [hMeq]
    _ ≤ ‖pm‖ * approximationNumber (BL.comp (S.comp AL)) k * ‖jm‖ :=
        approximationNumber_comp_comp_le jm (BL.comp (S.comp AL)) pm k
    _ ≤ 1 * approximationNumber (BL.comp (S.comp AL)) k * 1 :=
        mul_le_mul (mul_le_mul hp1 le_rfl hak zero_le_one) hj1 (norm_nonneg _)
          (mul_nonneg zero_le_one hak)
    _ = approximationNumber (BL.comp (S.comp AL)) k := by ring
    _ ≤ ‖BL‖ * ‖AL‖ * hilbertNumber S k :=
        approximationNumber_comp_comp_le_mul_hilbertNumber S AL BL k
    _ ≤ ‖B'‖ * ‖A'‖ * hilbertNumber S k := by
        have hBLn : ‖BL‖ ≤ ‖B'‖ :=
          (ContinuousLinearMap.opNorm_comp_le jm B').trans
            (mul_le_of_le_one_left (norm_nonneg _) hj1)
        have hALn : ‖AL‖ ≤ ‖A'‖ :=
          (ContinuousLinearMap.opNorm_comp_le A' pm).trans
            (mul_le_of_le_one_right (norm_nonneg _) hp1)
        exact mul_le_mul (mul_le_mul hBLn hALn (norm_nonneg _) (norm_nonneg _)) le_rfl
          (hilbertNumber_nonneg S k) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
end SNumbers
