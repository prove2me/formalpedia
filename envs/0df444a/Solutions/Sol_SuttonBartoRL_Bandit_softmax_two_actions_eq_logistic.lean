-- Prove2me | solution 1 for SuttonBartoRL.Bandit.softmax_two_actions_eq_logistic
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T09:31:07.462498+00:00
-- url     : https://prove2.me/submissions/cda7db1d-c591-4719-a6f0-2c8f3280cb33

import Mathlib
import Definitions.Def_SuttonBartoRL_Bandit_GradientBandit

open SuttonBartoRL.Bandit in
theorem solution (H : Fin 2 → ℝ) :
    softmaxPolicy H 0 = 1 / (1 + Real.exp (-(H 0 - H 1))) ∧
      softmaxPolicy H 1 = 1 / (1 + Real.exp (-(H 1 - H 0))) := by
  have h0 := Real.exp_pos (H 0)
  have h1 := Real.exp_pos (H 1)
  simp only [softmaxPolicy, Fin.sum_univ_two, neg_sub, Real.exp_sub]
  constructor
  · field_simp
  · field_simp
    ring
