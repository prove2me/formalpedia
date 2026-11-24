-- Prove2me | solution 1 for SameStatePairs.permutation_gauge
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-24T00:38:17.32873+00:00
-- url     : https://prove2.me/submissions/8bf0748f-a2ae-47d0-a881-6f9e4d74c4dd

import Mathlib
import Definitions.Def_SameStatePairs_Basic

set_option autoImplicit false

open Matrix

open SameStatePairs

private lemma perm_inv_eq {d : ℕ} (τ : Equiv.Perm (Fin d)) :
    (τ.permMatrix ℝ)⁻¹ = (τ⁻¹).permMatrix ℝ := by
  apply Matrix.inv_eq_right_inv
  rw [← Matrix.permMatrix_mul, inv_mul_cancel, Matrix.permMatrix_one]

private lemma perm_mul_inv {d : ℕ} (τ : Equiv.Perm (Fin d)) :
    τ.permMatrix ℝ * (τ⁻¹).permMatrix ℝ = 1 := by
  rw [← Matrix.permMatrix_mul, inv_mul_cancel, Matrix.permMatrix_one]

private lemma perm_inv_mul {d : ℕ} (τ : Equiv.Perm (Fin d)) :
    (τ⁻¹).permMatrix ℝ * τ.permMatrix ℝ = 1 := by
  rw [← Matrix.permMatrix_mul, mul_inv_cancel, Matrix.permMatrix_one]

theorem solution {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ) (hA : A.rank = d)
    (σ : Equiv.Perm (Fin d)) :
    (∀ z : Fin d → ℝ, A *ᵥ (σ.permMatrix ℝ *ᵥ z) = (A * σ.permMatrix ℝ) *ᵥ z) ∧
    (∀ σ₀ : Equiv.Perm (Fin d),
      (A * σ₀.permMatrix ℝ) * ((σ₀.permMatrix ℝ)⁻¹ * σ.permMatrix ℝ) = A * σ.permMatrix ℝ) ∧
    {AP : Matrix (Fin n) (Fin d) ℝ × Equiv.Perm (Fin d) |
      AP.1 * AP.2.permMatrix ℝ = A * σ.permMatrix ℝ}.ncard = d.factorial ∧
    (∀ AP : Matrix (Fin n) (Fin d) ℝ × Equiv.Perm (Fin d),
      AP.1 * AP.2.permMatrix ℝ = A * σ.permMatrix ℝ →
      ∃ σ₀ : Equiv.Perm (Fin d), AP.1 = A * σ₀.permMatrix ℝ ∧
        AP.2.permMatrix ℝ = (σ₀.permMatrix ℝ)⁻¹ * σ.permMatrix ℝ) := by
  -- the fibre over `τ` is forced: `AP.1 = A P_σ P_τ⁻¹ = A P_{τ⁻¹ σ}`
  have key : ∀ AP : Matrix (Fin n) (Fin d) ℝ × Equiv.Perm (Fin d),
      AP.1 * AP.2.permMatrix ℝ = A * σ.permMatrix ℝ ↔
        AP.1 = A * (AP.2⁻¹ * σ).permMatrix ℝ := by
    rintro ⟨M, τ⟩
    simp only
    rw [Matrix.permMatrix_mul]
    constructor
    · intro h
      rw [← Matrix.mul_assoc, ← h, Matrix.mul_assoc, perm_mul_inv, Matrix.mul_one]
    · intro h
      rw [h, Matrix.mul_assoc, Matrix.mul_assoc, perm_inv_mul, Matrix.mul_one]
  refine ⟨fun z => Matrix.mulVec_mulVec _ _ _, fun σ₀ => ?_, ?_, fun AP h => ?_⟩
  · rw [perm_inv_eq, Matrix.mul_assoc, ← Matrix.mul_assoc (σ₀.permMatrix ℝ), perm_mul_inv,
      Matrix.one_mul]
  · have hS : {AP : Matrix (Fin n) (Fin d) ℝ × Equiv.Perm (Fin d) |
        AP.1 * AP.2.permMatrix ℝ = A * σ.permMatrix ℝ} =
        Set.range (fun τ : Equiv.Perm (Fin d) => (A * (τ⁻¹ * σ).permMatrix ℝ, τ)) := by
      ext ⟨M, τ⟩
      simp only [Set.mem_range]
      rw [show ((M, τ) ∈ {AP : Matrix (Fin n) (Fin d) ℝ × Equiv.Perm (Fin d) |
        AP.1 * AP.2.permMatrix ℝ = A * σ.permMatrix ℝ}) ↔ _ from key (M, τ)]
      constructor
      · intro h; exact ⟨τ, by simp only at h; rw [h]⟩
      · rintro ⟨τ', h⟩
        simp only [Prod.mk.injEq] at h
        obtain ⟨h1, rfl⟩ := h
        exact h1.symm
    rw [hS, Set.ncard_range_of_injective, Nat.card_eq_fintype_card, Fintype.card_perm,
      Fintype.card_fin]
    intro a b hab
    exact (Prod.mk.inj hab).2
  · refine ⟨AP.2⁻¹ * σ, (key AP).1 h, ?_⟩
    rw [perm_inv_eq, ← Matrix.permMatrix_mul, _root_.mul_inv_rev, inv_inv, ← mul_assoc,
      mul_inv_cancel, one_mul]
