-- Prove2me | solution 1 for SNumbers.one_le_hilbertNumber_id
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:06:52.232632+00:00
-- url     : https://prove2.me/submissions/342e1f39-5ae3-4843-94ef-f8c49c8420c4

module
public import Definitions.Def_SNumbers_Approximation
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Definitions.Def_SNumbers_Hilbert
public import Theorems.Thm_SNumbers_ratio_le_hilbertNumber
public import Theorems.Thm_SNumbers_exists_l2_section
public import Theorems.Thm_ContinuousLinearMap_rank_zero
public import Theorems.Thm_SNumbers_approximationNumber_comp_comp_le
public import Theorems.Thm_SNumbers_approximationNumber_id_euclidean
public import Theorems.Thm_SNumbers_approximationNumber_nonneg
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
theorem _root_.solution (n : ℕ) :
    1 ≤ hilbertNumber (ContinuousLinearMap.id 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1)))) n := by
  obtain ⟨B, A, hAB, hA, hB⟩ := exists_l2_section (𝕜 := 𝕜) n
  have hidne : ContinuousLinearMap.id 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1))) ≠ 0 := by
    intro h
    have h2 : (EuclideanSpace.single (0 : Fin (n + 1)) (1 : 𝕜)) = 0 := by
      have h3 := DFunLike.congr_fun h (EuclideanSpace.single (0 : Fin (n + 1)) (1 : 𝕜))
      simp only [ContinuousLinearMap.id_apply, zero_apply] at h3
      exact h3
    rw [PiLp.single_eq_zero_iff] at h2
    exact one_ne_zero h2
  have hBne : B ≠ 0 := by
    rintro rfl; rw [ContinuousLinearMap.comp_zero] at hAB; exact hidne hAB.symm
  have hAne : A ≠ 0 := by
    rintro rfl; rw [ContinuousLinearMap.zero_comp] at hAB; exact hidne hAB.symm
  -- `id = A ∘ (B ∘ A) ∘ B`.
  have hfact : A.comp ((B.comp A).comp B) =
      ContinuousLinearMap.id 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1))) := by
    rw [ContinuousLinearMap.comp_assoc, hAB, ContinuousLinearMap.comp_id, hAB]
  -- `1 = aₙ(id) ≤ ‖A‖ · aₙ(B∘A) · ‖B‖`.
  have hid1 : (1 : ℝ) ≤ ‖A‖ * approximationNumber (B.comp A) n * ‖B‖ := by
    have h := approximationNumber_comp_comp_le B (B.comp A) A n
    rw [hfact, approximationNumber_id_euclidean] at h
    exact h
  have hsn := approximationNumber_nonneg (B.comp A) n
  -- hence `1 ≤ aₙ(B∘A)`.
  have e1 : ‖A‖ * approximationNumber (B.comp A) n ≤ approximationNumber (B.comp A) n := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hA) hsn]
  have hprod : ‖A‖ * approximationNumber (B.comp A) n * ‖B‖
      ≤ approximationNumber (B.comp A) n := by
    nlinarith [e1, mul_nonneg (mul_nonneg (norm_nonneg A) hsn) (sub_nonneg.mpr hB)]
  have haBA : (1 : ℝ) ≤ approximationNumber (B.comp A) n := le_trans hid1 hprod
  -- The ratio of the admissible pair `(A, B)` is `≥ 1`.
  have hratio := ratio_le_hilbertNumber
    (ContinuousLinearMap.id 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1)))) n hAne hBne
  rw [ContinuousLinearMap.id_comp] at hratio
  refine le_trans ?_ hratio
  rw [le_div_iff₀ (mul_pos (norm_pos_iff.mpr hBne) (norm_pos_iff.mpr hAne)), one_mul]
  calc ‖B‖ * ‖A‖
      ≤ 1 * 1 := mul_le_mul hB hA (norm_nonneg A) zero_le_one
    _ = 1 := one_mul 1
    _ ≤ approximationNumber (B.comp A) n := haBA
end SNumbers
