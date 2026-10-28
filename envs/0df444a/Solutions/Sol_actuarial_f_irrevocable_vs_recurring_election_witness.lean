-- Prove2me | solution 1 for actuarial_f_irrevocable_vs_recurring_election_witness
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:40:50.102159+00:00
-- url     : https://prove2.me/submissions/23c132fe-1dd1-42e0-a868-c38099e56eec

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
    fixedChoicePayment a b ga gb 0 0 +
        fixedChoicePayment a b ga gb 0 1 = 240 ∧
      max (a 0 * ga 0 + a 0 * ga 1)
          (b 0 * gb 0 + b 0 * gb 1) = 400 ∧
      annualFloorPayment a b ga gb 0 0 +
        annualFloorPayment a b ga gb 0 1 = 420 := by
  intro a b ga gb
  norm_num [a, b, ga, gb, fixedChoicePayment, annualFloorPayment] <;> grind
