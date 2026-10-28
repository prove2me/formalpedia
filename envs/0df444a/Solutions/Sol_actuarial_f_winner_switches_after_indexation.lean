-- Prove2me | solution 1 for actuarial_f_winner_switches_after_indexation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:36:45.259314+00:00
-- url     : https://prove2.me/submissions/aaec1364-f672-4b14-8b14-bdc0a14faaf2

import Mathlib


import Definitions.Def_actuarial_f_annualFloorPayment
import Definitions.Def_actuarial_f_fixedChoicePayment

open ActuarialUnderpinsF

theorem solution :
    let a : ℕ → ℝ := fun _ => 120
    let b : ℕ → ℝ := fun _ => 100
    let ga : ℕ → ℝ := fun _ => 1
    let gb : ℕ → ℝ := fun t => if t = 0 then 1 else 3
    fixedChoicePayment a b ga gb 0 1 = 120 ∧
      annualFloorPayment a b ga gb 0 1 = 300 :=
  by
  intro a b ga gb
  simp only [fixedChoicePayment, annualFloorPayment, a, b, ga, gb]
  norm_num
