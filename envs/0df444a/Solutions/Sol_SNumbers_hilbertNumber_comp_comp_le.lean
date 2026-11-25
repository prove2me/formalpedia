-- Prove2me | solution 1 for SNumbers.hilbertNumber_comp_comp_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:06:49.964803+00:00
-- url     : https://prove2.me/submissions/bd3afa3a-955b-4e35-86d6-e8df0619bf81

module
public import Definitions.Def_SNumbers_Approximation
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Definitions.Def_SNumbers_Hilbert
public import Theorems.Thm_SNumbers_hilbertNumber_def
public import Theorems.Thm_SNumbers_ratio_le_hilbertNumber
public import Theorems.Thm_SNumbers_hilbertNumber_nonneg
public import Theorems.Thm_ContinuousLinearMap_rank_zero
public import Theorems.Thm_SNumbers_approximationNumber_eq_zero_of_rank_le
public import Theorems.Thm_SNumbers_approximationNumber_zero_eq_norm
attribute [local simp] ContinuousLinearMap.rank_zero
attribute [local simp] SNumbers.approximationNumber_zero_eq_norm



set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped Cardinal
open ContinuousLinearMap
open SNumbers
variable {𝕜 : Type u} [RCLike 𝕜]
variable {X Y W Z : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [NormedAddCommGroup W] [NormedSpace 𝕜 W]
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
namespace SNumbers
theorem _root_.solution (A₀ : W →L[𝕜] X) (S : X →L[𝕜] Y) (B₀ : Y →L[𝕜] Z) (n : ℕ) :
    hilbertNumber (B₀.comp (S.comp A₀)) n ≤ ‖B₀‖ * hilbertNumber S n * ‖A₀‖ := by
  have hRHS : 0 ≤ ‖B₀‖ * hilbertNumber S n * ‖A₀‖ :=
    mul_nonneg (mul_nonneg (norm_nonneg _) (hilbertNumber_nonneg S n)) (norm_nonneg _)
  rw [hilbertNumber_def]
  refine Real.sSup_le ?_ hRHS
  rintro r ⟨A, B, hA, hB, rfl⟩
  have hpos : 0 < ‖B‖ * ‖A‖ := mul_pos (norm_pos_iff.mpr hB) (norm_pos_iff.mpr hA)
  -- Re-bracket `B ∘ (B₀ ∘ S ∘ A₀) ∘ A = (B ∘ B₀) ∘ S ∘ (A₀ ∘ A)`.
  have hcomp : B.comp ((B₀.comp (S.comp A₀)).comp A)
      = (B.comp B₀).comp (S.comp (A₀.comp A)) := by
    simp only [ContinuousLinearMap.comp_assoc]
  rw [hcomp]
  set B' := B.comp B₀ with hB'def
  set A' := A₀.comp A with hA'def
  have hb' : ‖B'‖ ≤ ‖B‖ * ‖B₀‖ := opNorm_comp_le B B₀
  have ha' : ‖A'‖ ≤ ‖A₀‖ * ‖A‖ := opNorm_comp_le A₀ A
  rw [div_le_iff₀ hpos]
  -- If either new factor is zero the composite vanishes, so `aₙ = 0`.
  by_cases hA'0 : A' = 0
  · have hz : B'.comp (S.comp A') = 0 := by rw [hA'0]; simp
    rw [hz, approximationNumber_eq_zero_of_rank_le (by simp)]
    exact mul_nonneg hRHS (by positivity)
  by_cases hB'0 : B' = 0
  · have hz : B'.comp (S.comp A') = 0 := by rw [hB'0]; simp
    rw [hz, approximationNumber_eq_zero_of_rank_le (by simp)]
    exact mul_nonneg hRHS (by positivity)
  -- Both nonzero: bound `a_n (B' S A')` by `h_n S · ‖B'‖ ‖A'‖`.
  have hkey : approximationNumber (B'.comp (S.comp A')) n ≤ hilbertNumber S n * (‖B'‖ * ‖A'‖) := by
    rw [← div_le_iff₀ (mul_pos (norm_pos_iff.mpr hB'0) (norm_pos_iff.mpr hA'0))]
    exact ratio_le_hilbertNumber S n hA'0 hB'0
  calc approximationNumber (B'.comp (S.comp A')) n
      ≤ hilbertNumber S n * (‖B'‖ * ‖A'‖) := hkey
    _ ≤ hilbertNumber S n * ((‖B‖ * ‖B₀‖) * (‖A₀‖ * ‖A‖)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul hb' ha' (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
          (hilbertNumber_nonneg S n)
    _ = (‖B₀‖ * hilbertNumber S n * ‖A₀‖) * (‖B‖ * ‖A‖) := by ring
end SNumbers
