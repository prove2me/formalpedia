-- Prove2me | solution 1 for SNumbers.le_sn_of_lt_approximationNumber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:20:39.599874+00:00
-- url     : https://prove2.me/submissions/7c80561e-8aa8-44fe-adc3-7e807a7a2063

module
public import Definitions.Def_SNumbers_Approximation
public import Definitions.Def_BasicResults_SVD
public import Definitions.Def_SNumbers_Uniqueness
public import Theorems.Thm_SNumbers_norm_smul_le_sn
public import Theorems.Thm_SVD_exists_scalar_factorisation


set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped Cardinal
open ContinuousLinearMap
open SNumbers
variable {𝕜 : Type u} [RCLike 𝕜]
variable {H₁ H₂ : Type u}
variable [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁] [CompleteSpace H₁]
variable [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂] [CompleteSpace H₂]
namespace SNumbers
theorem _root_.solution {s : Family 𝕜} (hs : IsSNumberSequence s)
    (S : H₁ →L[𝕜] H₂) (n : ℕ) {c : ℝ} (hc0 : 0 ≤ c)
    (hca : c < approximationNumber S n) : c ≤ s S n := by
  rcases hc0.eq_or_lt with hc | hcpos
  · -- `c = 0`: immediate from non-negativity (S1).
    rw [← hc]; exact hs.nonneg S n
  · -- `c > 0`: use the SVD factorisation.
    obtain ⟨A, B, hA, hB, hfact⟩ :=
      SVD.exists_scalar_factorisation S n hc0 hca
    have hc_ne : (c : 𝕜) ≠ 0 := by exact_mod_cast hcpos.ne'
    have hnorm : ‖(c : 𝕜)‖ = c := by rw [RCLike.norm_ofReal, abs_of_pos hcpos]
    -- (S5) normalisation on `ℓ₂ⁿ⁺¹`.
    have hid : s (ContinuousLinearMap.id 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1)))) n = 1 :=
      hs.normalised_at_id n
    -- Lower bound on `sₙ(c • id)` via reverse homogeneity.
    have hlow : c ≤ s ((c : 𝕜) •
        ContinuousLinearMap.id 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1)))) n := by
      have h := norm_smul_le_sn hs hc_ne
        (ContinuousLinearMap.id 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1)))) n
      rwa [hnorm, hid, mul_one] at h
    -- Upper bound on `sₙ(B ∘ S ∘ A)` via the (S3) ideal property.
    have hsn : 0 ≤ s S n := hs.nonneg S n
    have hupp : s (B.comp (S.comp A)) n ≤ s S n := by
      have h3 := hs.ideal A S B n
      have hb : ‖B‖ * s S n ≤ s S n := by nlinarith [hsn, hB, norm_nonneg B]
      have hba : ‖B‖ * s S n * ‖A‖ ≤ s S n := by
        nlinarith [hb, hA, mul_nonneg (norm_nonneg B) hsn, norm_nonneg A]
      linarith [h3]
    -- Combine: `c ≤ sₙ(c • id) = sₙ(B ∘ S ∘ A) ≤ sₙ(S)`.
    rw [hfact] at hupp
    linarith [hlow, hupp]
end SNumbers
