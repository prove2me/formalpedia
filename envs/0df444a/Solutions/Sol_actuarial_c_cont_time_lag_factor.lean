-- Prove2me | solution 1 for actuarial_c_cont_time_lag_factor
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T14:54:35.475362+00:00
-- url     : https://prove2.me/submissions/71f03e1c-c7a7-4e35-aee3-3d750c5ee44d

import Mathlib
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_cont_deathPV
import Definitions.Def_actuarial_c_cont_laggedDeathPV

open ActuarialAssurances.Continuous

open MeasureTheory


theorem solution (n delta lag t : ℝ) :
    laggedDeathPV n delta lag t =
      Real.exp (-delta * lag) * deathPV n delta t := by
  unfold laggedDeathPV deathPV
  split_ifs
  · rw [← Real.exp_add]; ring_nf
  · simp

