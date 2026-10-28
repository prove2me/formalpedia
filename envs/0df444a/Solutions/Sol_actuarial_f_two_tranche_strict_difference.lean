-- Prove2me | solution 1 for actuarial_f_two_tranche_strict_difference
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:39:13.921551+00:00
-- url     : https://prove2.me/submissions/0f29dbf9-ef37-441f-a876-3bd15b20db61

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_trancheFloorTotal
import Definitions.Def_actuarial_f_wholeFloorTotal

open ActuarialUnderpinsF

theorem solution :
    let a : ℕ → ℝ := fun i => if i = 0 then 10 else 0
    let b : ℕ → ℝ := fun i => if i = 1 then 10 else 0
    trancheFloorTotal a b 2 = 20 ∧ wholeFloorTotal a b 2 = 10 := by
  intro a b
  norm_num [a, b, trancheFloorTotal, wholeFloorTotal, awardBase, Finset.sum_range_succ] <;> grind
