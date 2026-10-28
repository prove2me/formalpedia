-- Prove2me | solution 1 for actuarial_f_expect_add
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:31:25.893065+00:00
-- url     : https://prove2.me/submissions/39dacced-8ff8-4d20-a302-d50ff4f7e4ac

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_expect

open ActuarialUnderpinsF

theorem solution (n h : ℕ) (p : ℕ → ℕ → ℕ → ℝ)
    (f g : ℕ → ℕ → ℕ → ℝ) :
    expect n h p (fun z i j => f z i j + g z i j) =
      expect n h p f + expect n h p g := by
  unfold expect ActuarialJointD.expect
  simp only [mul_add, Finset.sum_add_distrib]
