-- Prove2me | solution 1 for actuarial_f_two_regime_two_years
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:35:24.708504+00:00
-- url     : https://prove2.me/submissions/737b6c4f-29b8-42e8-aeb7-2e650ef9945b

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_phasedPension

open ActuarialUnderpinsF

theorem solution (base : ℝ) :
    phasedPension base 1 2 (fun _ => (2/100 : ℝ))
      (fun _ => (3/100 : ℝ)) = base * (102/100 : ℝ) * (103/100 : ℝ) := by
  norm_num [phasedPension, deferredIncrease, paymentIncrease, compoundGrowth, Finset.prod_range_succ] <;> grind
