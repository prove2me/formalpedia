-- Prove2me | solution 1 for actuarial_c_cont_death_amount_scale
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T14:50:41.489523+00:00
-- url     : https://prove2.me/submissions/bc4decf2-3e3c-4af3-b285-56378cd3dd90

import Mathlib
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_cont_deathPV
import Definitions.Def_actuarial_c_cont_sumAssuredDeathPV

open ActuarialAssurances.Continuous

open MeasureTheory


theorem solution (n delta amount t : ℝ) :
    sumAssuredDeathPV n delta amount t =
      amount * deathPV n delta t := by
  simp [ActuarialAssurances.Continuous.deathPV, ActuarialAssurances.Continuous.sumAssuredDeathPV]

