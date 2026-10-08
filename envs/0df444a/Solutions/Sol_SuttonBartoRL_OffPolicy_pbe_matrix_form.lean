-- Prove2me | solution 1 for SuttonBartoRL.OffPolicy.pbe_matrix_form
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T15:33:22.694362+00:00
-- url     : https://prove2.me/submissions/dc07c461-bcd2-4114-a084-3ad593149ed1

import Mathlib
import Definitions.Def_SuttonBartoRL_OffPolicy_LinearGeometry

open Matrix

namespace PBE7bc8

lemma muNormSq_eq {S : Type} [Fintype S] [DecidableEq S] (μ : S → ℝ) (v : S → ℝ) :
    SuttonBartoRL.OffPolicy.muNormSq μ v = v ⬝ᵥ (SuttonBartoRL.OffPolicy.Dmat μ *ᵥ v) := by
  unfold SuttonBartoRL.OffPolicy.muNormSq SuttonBartoRL.OffPolicy.Dmat
  simp only [dotProduct, mulVec_diagonal]
  refine Finset.sum_congr rfl fun s _ => ?_
  ring

lemma core {S : Type} [Fintype S] [DecidableEq S] {d : ℕ} (μ : S → ℝ)
    (X : Matrix S (Fin d) ℝ) (hX : IsUnit (Xᵀ * diagonal μ * X).det) (δ : S → ℝ) :
    ((X * (Xᵀ * diagonal μ * X)⁻¹ * Xᵀ * diagonal μ) *ᵥ δ) ⬝ᵥ
        (diagonal μ *ᵥ ((X * (Xᵀ * diagonal μ * X)⁻¹ * Xᵀ * diagonal μ) *ᵥ δ))
      = (Xᵀ *ᵥ (diagonal μ *ᵥ δ)) ⬝ᵥ ((Xᵀ * diagonal μ * X)⁻¹ *ᵥ (Xᵀ *ᵥ (diagonal μ *ᵥ δ)))
    ∧ δ ⬝ᵥ ((diagonal μ * X * (Xᵀ * diagonal μ * X)⁻¹ * Xᵀ * diagonal μ) *ᵥ δ)
      = (Xᵀ *ᵥ (diagonal μ *ᵥ δ)) ⬝ᵥ ((Xᵀ * diagonal μ * X)⁻¹ *ᵥ (Xᵀ *ᵥ (diagonal μ *ᵥ δ))) := by
  set G := Xᵀ * diagonal μ * X with hGdef
  set u := Xᵀ *ᵥ (diagonal μ *ᵥ δ) with hu
  set y := G⁻¹ *ᵥ u with hy
  have hD : (diagonal μ)ᵀ = diagonal μ := diagonal_transpose μ
  have hPi : (X * G⁻¹ * Xᵀ * diagonal μ) *ᵥ δ = X *ᵥ y := by
    simp only [hy, hu, mulVec_mulVec, Matrix.mul_assoc]
  have hGy : G *ᵥ y = u := by
    rw [hy, mulVec_mulVec, mul_nonsing_inv _ hX, one_mulVec]
  refine ⟨?_, ?_⟩
  · rw [hPi]
    have : (X *ᵥ y) ⬝ᵥ (diagonal μ *ᵥ (X *ᵥ y)) = y ⬝ᵥ (G *ᵥ y) := by
      rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, dotProduct_comm]
      simp only [hGdef, mulVec_mulVec, Matrix.mul_assoc]
    rw [this, hGy, dotProduct_comm]
  · have : (diagonal μ * X * G⁻¹ * Xᵀ * diagonal μ) *ᵥ δ = diagonal μ *ᵥ (X *ᵥ y) := by
      simp only [hy, hu, mulVec_mulVec, Matrix.mul_assoc]
    rw [this, dotProduct_mulVec, ← mulVec_transpose, hD, dotProduct_mulVec, ← mulVec_transpose]

end PBE7bc8

open SuttonBartoRL.OffPolicy Matrix in
theorem solution {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] {d : ℕ}
    (M : MDP S A) (π : SuttonBartoRL.FiniteMDP.Policy S A) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (μ : S → ℝ) (hμ0 : ∀ s, 0 ≤ μ s) (hμ1 : ∑ s, μ s = 1)
    (X : Matrix S (Fin d) ℝ) (hX : IsUnit (Xᵀ * Dmat μ * X).det) (w : Fin d → ℝ) :
    PBE M π γ μ X w
        = bellmanError M π γ X w ⬝ᵥ
            ((Dmat μ * X * (Xᵀ * Dmat μ * X)⁻¹ * Xᵀ * Dmat μ) *ᵥ bellmanError M π γ X w) ∧
    PBE M π γ μ X w
        = (Xᵀ *ᵥ (Dmat μ *ᵥ bellmanError M π γ X w)) ⬝ᵥ
            ((Xᵀ * Dmat μ * X)⁻¹ *ᵥ (Xᵀ *ᵥ (Dmat μ *ᵥ bellmanError M π γ X w))) := by
  have h := PBE7bc8.core μ X hX (bellmanError M π γ X w)
  have hP : PBE M π γ μ X w
      = ((X * (Xᵀ * diagonal μ * X)⁻¹ * Xᵀ * diagonal μ) *ᵥ bellmanError M π γ X w) ⬝ᵥ
        (diagonal μ *ᵥ ((X * (Xᵀ * diagonal μ * X)⁻¹ * Xᵀ * diagonal μ) *ᵥ bellmanError M π γ X w)) := by
    unfold PBE
    rw [PBE7bc8.muNormSq_eq]
    rfl
  simp only [Dmat] at hX ⊢
  rw [hP]
  exact ⟨h.1.trans h.2.symm, h.1⟩
