-- Prove2me | solution 2 for actuarial_f_winner_switches_after_indexation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:37:00.987356+00:00
-- url     : https://prove2.me/submissions/e75864ae-16a4-4525-973c-cba05965b05b

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_annualFloorPayment
import Definitions.Def_actuarial_f_fixedChoicePayment

open ActuarialUnderpinsF

theorem solution :
    let a : ℕ → ℝ := fun _ => 120
    let b : ℕ → ℝ := fun _ => 100
    let ga : ℕ → ℝ := fun _ => 1
    let gb : ℕ → ℝ := fun t => if t = 0 then 1 else 3
    fixedChoicePayment a b ga gb 0 1 = 120 ∧
      annualFloorPayment a b ga gb 0 1 = 300 := by
  intro a b ga gb
  norm_num [a, b, ga, gb, fixedChoicePayment, annualFloorPayment] <;> grind
