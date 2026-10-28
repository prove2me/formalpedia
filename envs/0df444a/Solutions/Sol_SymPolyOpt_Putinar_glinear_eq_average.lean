-- Prove2me | solution 1 for SymPolyOpt.Putinar.glinear_eq_average
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T00:58:59.741517+00:00
-- url     : https://prove2.me/submissions/24442a3c-d41d-44e4-a0da-b245cb7a22bc

import Mathlib
import Definitions.Def_SymPolyOpt_Putinar_Setting

open MvPolynomial SymPolyOpt.Putinar in
theorem solution {n : ℕ} (G : Subgroup (GL (Fin n) ℝ)) [Fintype G]
    (L : MvPolynomial (Fin n) ℝ →ₗ[ℝ] ℝ) (hL : IsGLinear G L) (p : MvPolynomial (Fin n) ℝ) :
    L p = (1 / (Fintype.card G : ℝ)) * ∑ σ : G, L (polyAct (σ : GL (Fin n) ℝ) p) ∧
      L p = L ((1 / (Fintype.card G : ℝ)) • ∑ σ : G, polyAct (σ : GL (Fin n) ℝ) p) := by
  have h : ∀ σ : G, L (polyAct (σ : GL (Fin n) ℝ) p) = L p := fun σ => (hL σ σ.2 p).symm
  have hc : (0 : ℝ) < Fintype.card G := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨1⟩
  have h1 : L p = (1 / (Fintype.card G : ℝ)) * ∑ σ : G, L (polyAct (σ : GL (Fin n) ℝ) p) := by
    simp only [h, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [one_div, ← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]
  refine ⟨h1, ?_⟩
  rw [map_smul, map_sum, smul_eq_mul]
  exact h1
