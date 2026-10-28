-- Prove2me | solution 1 for actuarial_f_two_state_expected_strict
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:36:56.22701+00:00
-- url     : https://prove2.me/submissions/6b9d4b9a-bef5-4fee-9ec2-1eeb44306fe6

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_awardBase
import Definitions.Def_actuarial_f_expect

open ActuarialUnderpinsF

theorem solution :
    let p : ℕ → ℕ → ℕ → ℝ := fun z i j =>
      if i = 0 ∧ j = 0 ∧ z < 2 then (1/2 : ℝ) else 0
    let a : ℕ → ℝ := fun z => if z = 0 then 100 else 0
    let b : ℕ → ℝ := fun z => if z = 1 then 100 else 0
    expect 2 0 p (fun z i j => awardBase a b z) = 100 ∧
      max (expect 2 0 p (fun z i j => a z))
          (expect 2 0 p (fun z i j => b z)) = 50 := by
  intro p a b
  norm_num [p, a, b, expect, ActuarialJointD.expect, awardBase, Finset.sum_range_succ] <;> grind
