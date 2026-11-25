-- Prove2me | solution 1 for SNumbers.approximationNumber_comp_comp_le_mul_hilbertNumber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:18:33.504511+00:00
-- url     : https://prove2.me/submissions/26307415-e8f6-48a8-b5ca-b6fb1bfb0014

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
public import Theorems.Thm_ContinuousLinearMap_rank_zero
public import Theorems.Thm_John_rankOneSA_apply
public import Theorems.Thm_SNumbers_Complexification_adjoint_complexify
public import Theorems.Thm_SNumbers_Complexification_complexify_conj
public import Theorems.Thm_SNumbers_Complexification_complexify_fst
public import Theorems.Thm_SNumbers_Complexification_complexify_ofReal
public import Theorems.Thm_SNumbers_Complexification_complexify_snd
public import Theorems.Thm_SNumbers_Complexification_norm_complexify
public import Theorems.Thm_SNumbers_approximationNumber_le_norm
public import Theorems.Thm_SNumbers_approximationNumber_zero_eq_norm
public import Theorems.Thm_SNumbers_bernsteinNumber_zero_eq_norm
public import Theorems.Thm_SNumbers_ratio_le_hilbertNumber
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
theorem _root_.solution
    (S : X →L[𝕜] Y) (A : L2 𝕜 →L[𝕜] X) (B : Y →L[𝕜] L2 𝕜) (n : ℕ) :
    approximationNumber (B.comp (S.comp A)) n ≤ ‖B‖ * ‖A‖ * hilbertNumber S n := by
  rcases eq_or_ne A 0 with rfl | hA
  · rw [ContinuousLinearMap.comp_zero, ContinuousLinearMap.comp_zero, norm_zero,
      mul_zero, zero_mul]
    simpa using approximationNumber_le_norm (0 : L2 𝕜 →L[𝕜] L2 𝕜) n
  rcases eq_or_ne B 0 with rfl | hB
  · rw [ContinuousLinearMap.zero_comp, norm_zero, zero_mul, zero_mul]
    simpa using approximationNumber_le_norm (0 : L2 𝕜 →L[𝕜] L2 𝕜) n
  · have hpos : 0 < ‖B‖ * ‖A‖ := mul_pos (norm_pos_iff.mpr hB) (norm_pos_iff.mpr hA)
    have h := ratio_le_hilbertNumber S n hA hB
    rw [div_le_iff₀ hpos] at h
    exact h.trans_eq (by ring)
end SNumbers
