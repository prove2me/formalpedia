-- Prove2me | solution 1 for actuarial_f_additive_and_compound_differ
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:40:44.903124+00:00
-- url     : https://prove2.me/submissions/123fe350-93b1-4f17-bd40-49c5ef43398e

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_additiveGrowth
import Definitions.Def_actuarial_f_compoundGrowth

open ActuarialUnderpinsF

theorem solution :
    additiveGrowth (fun _ => (1/10 : ℝ)) 2 = (6/5 : ℝ) ∧
      compoundGrowth (fun _ => (1/10 : ℝ)) 2 = (121/100 : ℝ) := by
  norm_num [additiveGrowth, compoundGrowth, Finset.sum_range_succ, Finset.prod_range_succ] <;> grind
