-- Prove2me | solution 1 for actuarial_c_delay_composition
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T15:00:34.294427+00:00
-- url     : https://prove2.me/submissions/eb9200d4-4880-49c7-878b-1bd311349751

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_death
import Definitions.Def_actuarial_c_delayPath
import Definitions.Def_actuarial_c_delayEPV

open ActuarialAssurances


theorem solution (h a b : ℕ) (v : ℝ) (benefit p : ℕ → ℝ) : delayEPV h (a+b) v benefit p=v^b*delayEPV h a v benefit p := by
  simp only [ActuarialAssurances.death, ActuarialAssurances.delayEPV, ActuarialAssurances.delayPath]
  simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  repeat refine Finset.sum_congr rfl fun _ _ => ?_
  beta_reduce
  split_ifs <;> ring

