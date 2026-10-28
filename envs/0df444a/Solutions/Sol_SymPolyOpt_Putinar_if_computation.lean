-- Prove2me | solution 1 for SymPolyOpt.Putinar.if_computation
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T01:52:22.779324+00:00
-- url     : https://prove2.me/submissions/367791c8-d0d2-4a46-ab43-0a03a4398175

import Mathlib
import Definitions.Def_SymPolyOpt_Putinar_Setting

open MvPolynomial

open SymPolyOpt.Putinar in
theorem solution {n : ℕ} (G : Subgroup (GL (Fin n) ℝ)) [Fintype G]
    (L : MvPolynomial (Fin n) ℝ →ₗ[ℝ] ℝ) (hL : IsGLinear G L)
    (gj : MvPolynomial (Fin n) ℝ) (hgj : IsGInvariant G gj) (h : MvPolynomial (Fin n) ℝ) :
    symForm G L gj h h = L (h * h * gj) := by
  have key : ∀ σ : G, polyAct (σ : GL (Fin n) ℝ) (h * h) * gj
      = polyAct (σ : GL (Fin n) ℝ) (h * h * gj) := by
    intro σ
    have hσ := hgj σ σ.2
    unfold polyAct at hσ ⊢
    rw [map_mul _ (h * h) gj, hσ]
  have inv : ∀ σ : G, L (polyAct (σ : GL (Fin n) ℝ) (h * h * gj)) = L (h * h * gj) :=
    fun σ => (hL σ σ.2 _).symm
  have hc : (Fintype.card G : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  unfold symForm
  simp_rw [key]
  rw [map_smul, map_sum]
  simp_rw [inv]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, smul_eq_mul, ← mul_assoc, one_div,
    inv_mul_cancel₀ hc, one_mul]
