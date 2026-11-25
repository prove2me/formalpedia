-- Prove2me | solution 1 for SNumbers.approximationNumber_le_two_mul_entropyNumber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:22:43.900258+00:00
-- url     : https://prove2.me/submissions/3ea8c8f9-b60b-48cd-bc7d-5c05ba159d17

module
public import Definitions.Def_SNumbers_Entropy
public import Definitions.Def_SNumbers_Inequalities
public import Definitions.Def_SNumbers_MaxDifference
public import Definitions.Def_BasicResults_SVD
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Definitions.Def_SNumbers_EntropyBounds
public import Theorems.Thm_SNumbers_half_le_entropyNumber_id
public import Theorems.Thm_ContinuousLinearMap_rank_zero
public import Theorems.Thm_John_rankOneSA_apply
public import Theorems.Thm_P2M_SNumbers_finrank_euclideanSpace_fin__a8e0c4e81f72
public import Theorems.Thm_SNumbers_Complexification_adjoint_complexify
public import Theorems.Thm_SNumbers_Complexification_complexify_conj
public import Theorems.Thm_SNumbers_Complexification_complexify_fst
public import Theorems.Thm_SNumbers_Complexification_complexify_ofReal
public import Theorems.Thm_SNumbers_Complexification_complexify_snd
public import Theorems.Thm_SNumbers_Complexification_norm_complexify
public import Theorems.Thm_SNumbers_approximationNumber_zero_eq_norm
public import Theorems.Thm_SNumbers_bernsteinNumber_zero_eq_norm
public import Theorems.Thm_SNumbers_entropyNumber_comp_comp_le
public import Theorems.Thm_SNumbers_entropyNumber_nonneg
public import Theorems.Thm_SNumbers_entropyNumber_zero_op
public import Theorems.Thm_SNumbers_padFin_apply
public import Theorems.Thm_SVD_exists_scalar_factorisation
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
attribute [local simp] SNumbers.entropyNumber_zero_op
attribute [local simp] SNumbers.padFin_apply
attribute [local simp] Submodule.liftQL_mkQL



set_option autoImplicit true
@[expose] public section
public section
universe u
open Filter Topology
open scoped Cardinal ENNReal
open ContinuousLinearMap
open SNumbers
variable {𝕜 : Type u} [RCLike 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable {H₁ H₂ : Type u}
variable [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁] [CompleteSpace H₁]
variable [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂] [CompleteSpace H₂]
namespace SNumbers
theorem _root_.solution (T : H₁ →L[𝕜] H₂) (n : ℕ) :
    approximationNumber T n ≤ 2 * entropyNumber T n := by
  by_contra hcon
  obtain ⟨γ, hγ1, hγ2⟩ := exists_between (not_le.mp hcon)
  have hγ0 : 0 < γ :=
    lt_of_le_of_lt (by positivity [entropyNumber_nonneg T n]) hγ1
  obtain ⟨A, B, hA, hB, hfact⟩ := SVD.exists_scalar_factorisation T n hγ0.le hγ2
  have hγ𝕜 : ((γ : ℝ) : 𝕜) ≠ 0 := by
    simpa using (RCLike.ofReal_ne_zero (K := 𝕜)).mpr (ne_of_gt hγ0)
  -- Rescale `B` so that the composition is exactly the identity.
  set B' : H₂ →L[𝕜] EuclideanSpace 𝕜 (Fin (n + 1)) := (((γ : ℝ) : 𝕜)⁻¹) • B with hB'
  have hcomp : B'.comp (T.comp A) =
      ContinuousLinearMap.id 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1))) := by
    rw [hB', ContinuousLinearMap.smul_comp, hfact, smul_smul,
      inv_mul_cancel₀ hγ𝕜, one_smul]
  have hB'norm : ‖B'‖ ≤ γ⁻¹ := by
    rw [hB', norm_smul, norm_inv, RCLike.norm_ofReal, abs_of_pos hγ0]
    calc γ⁻¹ * ‖B‖ ≤ γ⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left hB (by positivity)
      _ = γ⁻¹ := mul_one _
  -- The identity on `ℓ₂ⁿ⁺¹` has entropy numbers at least `1/2`.
  have hid : 1 / 2 ≤ entropyNumber
      (ContinuousLinearMap.id 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1)))) n := by
    refine half_le_entropyNumber_id _ ?_
    rw [finrank_euclideanSpace_fin']
    exact Nat.lt_succ_self n
  rw [← hcomp] at hid
  have hchain : entropyNumber (B'.comp (T.comp A)) n ≤ γ⁻¹ * entropyNumber T n := by
    have h0 : (0 : ℝ) ≤ entropyNumber T n := entropyNumber_nonneg T n
    calc entropyNumber (B'.comp (T.comp A)) n
        ≤ ‖B'‖ * entropyNumber T n * ‖A‖ := entropyNumber_comp_comp_le B' T A n
      _ ≤ γ⁻¹ * entropyNumber T n * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_right hB'norm h0) hA (norm_nonneg A)
            (mul_nonneg (inv_pos.mpr hγ0).le h0)
      _ = γ⁻¹ * entropyNumber T n := mul_one _
  have hfinal : γ ≤ 2 * entropyNumber T n := by
    have h1 : 1 / 2 ≤ γ⁻¹ * entropyNumber T n := hid.trans hchain
    have h2 : γ * γ⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hγ0)
    nlinarith [h1, h2, hγ0, entropyNumber_nonneg T n]
  linarith
end SNumbers
