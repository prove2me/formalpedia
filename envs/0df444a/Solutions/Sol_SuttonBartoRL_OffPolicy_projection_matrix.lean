-- Prove2me | solution 1 for SuttonBartoRL.OffPolicy.projection_matrix
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T02:56:09.684962+00:00
-- url     : https://prove2.me/submissions/ef80ee39-c2ef-4713-89b7-a29723b6e1ba

import Mathlib
import Definitions.Def_SuttonBartoRL_OffPolicy_LinearGeometry

set_option autoImplicit false

open Matrix

namespace SuttonBartoRL.OffPolicy.D753

lemma muNormSq_add_of_orth {S : Type} [Fintype S] (μ : S → ℝ) (a b : S → ℝ)
    (h : ∑ s, μ s * a s * b s = 0) :
    muNormSq μ (a + b) = muNormSq μ a + muNormSq μ b := by
  unfold muNormSq
  simp only [Pi.add_apply]
  have e : ∀ s, μ s * (a s + b s) ^ 2 = μ s * a s ^ 2 + μ s * b s ^ 2 + 2 * (μ s * a s * b s) := by
    intro s; ring
  simp_rw [e, Finset.sum_add_distrib, ← Finset.mul_sum, h]
  ring

lemma muNormSq_nonneg' {S : Type} [Fintype S] (μ : S → ℝ) (hμ0 : ∀ s, 0 ≤ μ s) (a : S → ℝ) :
    0 ≤ muNormSq μ a := by
  unfold muNormSq
  exact Finset.sum_nonneg fun s _ => mul_nonneg (hμ0 s) (sq_nonneg _)

lemma orth {S : Type} [Fintype S] [DecidableEq S] {d : ℕ} (μ : S → ℝ)
    (X : Matrix S (Fin d) ℝ) (r : S → ℝ) (hr : Xᵀ *ᵥ (Dmat μ *ᵥ r) = 0) (w : Fin d → ℝ) :
    ∑ s, μ s * r s * (X *ᵥ w) s = 0 := by
  have h1 : (Dmat μ *ᵥ r) ⬝ᵥ (X *ᵥ w) = (Xᵀ *ᵥ (Dmat μ *ᵥ r)) ⬝ᵥ w := by
    rw [dotProduct_mulVec, mulVec_transpose]
  rw [hr, zero_dotProduct] at h1
  rw [← h1]
  simp only [dotProduct, Dmat, mulVec_diagonal]

end SuttonBartoRL.OffPolicy.D753

open Matrix SuttonBartoRL.OffPolicy in
theorem solution {S : Type} [Fintype S] [DecidableEq S] {d : ℕ}
    (μ : S → ℝ) (hμ0 : ∀ s, 0 ≤ μ s) (hμ1 : ∑ s, μ s = 1)
    (X : Matrix S (Fin d) ℝ) (hX : IsUnit (Xᵀ * Dmat μ * X).det) (v : S → ℝ) :
    (∀ u : Fin d → ℝ, muNormSq μ (v - projMatrix μ X *ᵥ v) ≤ muNormSq μ (v - vw X u)) ∧
    (∀ u : Fin d → ℝ, (∀ u' : Fin d → ℝ, muNormSq μ (v - vw X u) ≤ muNormSq μ (v - vw X u')) →
      u = (Xᵀ * Dmat μ * X)⁻¹ *ᵥ (Xᵀ *ᵥ (Dmat μ *ᵥ v)) ∧ vw X u = projMatrix μ X *ᵥ v) ∧
    (projMatrix μ X)ᵀ * Dmat μ * projMatrix μ X
      = Dmat μ * X * (Xᵀ * Dmat μ * X)⁻¹ * Xᵀ * Dmat μ := by
  set D := Dmat μ with hD
  set A := Xᵀ * D * X with hA
  set us := A⁻¹ *ᵥ (Xᵀ *ᵥ (D *ᵥ v)) with hus
  have hP : projMatrix μ X *ᵥ v = X *ᵥ us := by
    show (X * A⁻¹ * Xᵀ * D) *ᵥ v = X *ᵥ us
    simp only [hus, mulVec_mulVec, Matrix.mul_assoc]
  have hAA : A * A⁻¹ = 1 := mul_nonsing_inv A hX
  have hAA' : A⁻¹ * A = 1 := nonsing_inv_mul A hX
  have hres : Xᵀ *ᵥ (D *ᵥ (v - X *ᵥ us)) = 0 := by
    have : Xᵀ *ᵥ (D *ᵥ (X *ᵥ us)) = Xᵀ *ᵥ (D *ᵥ v) := by
      rw [mulVec_mulVec, mulVec_mulVec, hus, mulVec_mulVec, ← hA, hAA, one_mulVec]
    rw [mulVec_sub, mulVec_sub, this, sub_self]
  -- decomposition
  have hdec : ∀ u : Fin d → ℝ, muNormSq μ (v - vw X u)
      = muNormSq μ (v - X *ᵥ us) + muNormSq μ (X *ᵥ (us - u)) := by
    intro u
    have : v - vw X u = (v - X *ᵥ us) + X *ᵥ (us - u) := by
      simp only [vw, mulVec_sub]; abel
    rw [this]
    exact D753.muNormSq_add_of_orth μ _ _ (D753.orth μ X _ hres _)
  refine ⟨?_, ?_, ?_⟩
  · intro u
    rw [hP, hdec u]
    linarith [D753.muNormSq_nonneg' μ hμ0 (X *ᵥ (us - u))]
  · intro u hu
    have h1 := hu us
    have h2 : muNormSq μ (v - vw X us) = muNormSq μ (v - X *ᵥ us) := rfl
    rw [hdec u, h2] at h1
    have h0 : muNormSq μ (X *ᵥ (us - u)) = 0 :=
      le_antisymm (by linarith) (D753.muNormSq_nonneg' μ hμ0 _)
    have hz : ∀ s, μ s * (X *ᵥ (us - u)) s = 0 := by
      intro s
      have hs := (Finset.sum_eq_zero_iff_of_nonneg
        (fun s _ => mul_nonneg (hμ0 s) (sq_nonneg ((X *ᵥ (us - u)) s)))).1 h0 s
        (Finset.mem_univ s)
      have : (μ s * (X *ᵥ (us - u)) s) ^ 2 = 0 := by
        have : (μ s * (X *ᵥ (us - u)) s) ^ 2 = μ s * (μ s * (X *ᵥ (us - u)) s ^ 2) := by ring
        rw [this, hs, mul_zero]
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
    have hDz : D *ᵥ (X *ᵥ (us - u)) = 0 := by
      funext s
      simp only [hD, Dmat, mulVec_diagonal, Pi.zero_apply]
      exact hz s
    have hAz : A *ᵥ (us - u) = 0 := by
      rw [hA, ← mulVec_mulVec, ← mulVec_mulVec, hDz, mulVec_zero]
    have hw : us - u = 0 := by
      rw [← one_mulVec (us - u), ← hAA', ← mulVec_mulVec, hAz, mulVec_zero]
    have hu' : u = us := (sub_eq_zero.1 hw).symm
    refine ⟨hu', ?_⟩
    rw [hP, hu']
    rfl
  · have hDt : Dᵀ = D := by simp [hD, Dmat]
    have hAt : Aᵀ = A := by
      rw [hA, transpose_mul, transpose_mul, transpose_transpose, hDt, Matrix.mul_assoc]
    have hAi : (A⁻¹)ᵀ = A⁻¹ := by rw [transpose_nonsing_inv, hAt]
    show (X * A⁻¹ * Xᵀ * D)ᵀ * D * (X * A⁻¹ * Xᵀ * D) = D * X * A⁻¹ * Xᵀ * D
    rw [transpose_mul, transpose_mul, transpose_mul, transpose_transpose, hDt, hAi]
    calc D * (X * (A⁻¹ * Xᵀ)) * D * (X * A⁻¹ * Xᵀ * D)
        = D * X * (A⁻¹ * (Xᵀ * D * X) * A⁻¹) * Xᵀ * D := by
          simp only [Matrix.mul_assoc]
      _ = D * X * A⁻¹ * Xᵀ * D := by
          rw [← hA, hAA', Matrix.one_mul]
