-- Prove2me | solution 1 for Rudin.ch05_taylor
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-13T14:39:09.290914+00:00
-- url     : https://prove2.me/submissions/f71ecba0-6ccd-455d-bcd7-3e3129ea036c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.


import Theorems.Thm_Rudin_ch05_taylor_helper

open Rudin

theorem solution (a b : ℝ) (hab : a < b) (f : ℝ → ℝ) (n : ℕ) (hn : 0 < n)
    (hcont : ContinuousOn (iteratedDeriv (n - 1) f) (Set.Icc a b))
    (hderiv : ∀ t ∈ Set.Ioo a b, DifferentiableAt ℝ (iteratedDeriv (n - 1) f) t)
    (α β : ℝ) (hα : α ∈ Set.Icc a b) (hβ : β ∈ Set.Icc a b) (hne : α ≠ β) :
    ∃ x : ℝ, ((α < x ∧ x < β) ∨ (β < x ∧ x < α)) ∧
      f β = (∑ k ∈ Finset.range n, iteratedDeriv k f α / (k.factorial : ℝ) * (β - α) ^ k)
        + iteratedDeriv n f x / (n.factorial : ℝ) * (β - α) ^ n := by
  exact ch05_taylor_helper a b hab f n hn hcont hderiv α β hα hβ hne
