-- Prove2me | solution 1 for ShannoCG.SCONB.restart_step_orth_grad
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T06:27:59.949542+00:00
-- url     : https://prove2.me/submissions/41dfa6f6-d37d-4eef-b03a-5badd315c2d0

import Mathlib
open Matrix

theorem solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (c : Fin n → ℝ)
    (x p g : ℕ → Fin n → ℝ) (t k : ℕ) (htk : t < k)
    (hg : ∀ i, g i = A *ᵥ x i + c)
    (hstep : ∀ i, t ≤ i → i ≤ k → x (i + 1) = x i + p i)
    (hexact_t : p t ⬝ᵥ g (t + 1) = 0)
    (hconj : ∀ i, t < i → i ≤ k → p t ⬝ᵥ (A *ᵥ p i) = 0) :
    p t ⬝ᵥ g (k + 1) = 0 := by
  have hi : ∀ i, t ≤ i → i ≤ k → p t ⬝ᵥ g (i + 1) = 0 := by
    intro i hti
    induction i, hti using Nat.le_induction with
    | base => intro _; exact hexact_t
    | succ i hti ih =>
      intro hik
      have hgstep : g (i + 1 + 1) = g (i + 1) + A *ᵥ p (i + 1) := by
        rw [hg, hg, hstep (i + 1) (by omega) hik, mulVec_add]
        abel
      rw [hgstep, dotProduct_add, ih (by omega), hconj (i + 1) (by omega) hik]
      simp
  exact hi k htk.le le_rfl
