-- Prove2me | solution 1 for ShannoCG.SCONB.grad_eq_add_sum
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T06:27:59.224571+00:00
-- url     : https://prove2.me/submissions/d7ed447e-5681-4b17-97e7-1f76fa8ceb63

import Mathlib
open Matrix

theorem solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (c : Fin n → ℝ)
    (x p g : ℕ → Fin n → ℝ) (t k : ℕ) (htk : t < k)
    (hg : ∀ i, g i = A *ᵥ x i + c)
    (hstep : ∀ i, t < i → i ≤ k → x (i + 1) = x i + p i) :
    g (k + 1) = A *ᵥ (x (t + 1) + ∑ i ∈ Finset.Ioc t k, p i) + c ∧
      g (k + 1) = g (t + 1) + ∑ i ∈ Finset.Ioc t k, A *ᵥ p i := by
  have hs : ∀ j, t ≤ j → j ≤ k → x (j + 1) = x (t + 1) + ∑ i ∈ Finset.Ioc t j, p i := by
    intro j htj
    induction j, htj using Nat.le_induction with
    | base => intro _; simp
    | succ j htj ih =>
      intro hj
      rw [hstep (j + 1) (by omega) hj, ih (by omega), Finset.sum_Ioc_succ_top htj]
      abel
  have hx := hs k htk.le le_rfl
  constructor
  · rw [hg, hx]
  · rw [hg, hx, mulVec_add, mulVec_sum, hg]
    abel
