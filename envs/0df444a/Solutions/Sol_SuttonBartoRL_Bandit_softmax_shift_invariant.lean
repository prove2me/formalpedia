-- Prove2me | solution 1 for SuttonBartoRL.Bandit.softmax_shift_invariant
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T09:49:04.502689+00:00
-- url     : https://prove2.me/submissions/0bfd5e36-a0e6-4ced-a733-b6e7a222cb06

import Mathlib
import Definitions.Def_SuttonBartoRL_Bandit_GradientBandit

open SuttonBartoRL.Bandit in
theorem solution {k : ℕ} (H : Fin k → ℝ) (c : ℝ) (a : Fin k) :
    softmaxPolicy (fun b => H b + c) a = softmaxPolicy H a := by
  unfold softmaxPolicy
  simp only [Real.exp_add]
  rw [← Finset.sum_mul, mul_div_mul_right _ _ (Real.exp_pos c).ne']
