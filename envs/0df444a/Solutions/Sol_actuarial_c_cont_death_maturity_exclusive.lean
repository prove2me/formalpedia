-- Prove2me | solution 1 for actuarial_c_cont_death_maturity_exclusive
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T14:51:00.080193+00:00
-- url     : https://prove2.me/submissions/9bebc833-f597-4fcd-9878-0f9916c7e53c

import Mathlib
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_cont_deathPV
import Definitions.Def_actuarial_c_cont_maturityPV

open ActuarialAssurances.Continuous

open MeasureTheory


theorem solution (n delta t : ℝ) :
    deathPV n delta t * maturityPV n delta t = 0 := by
  simp only [ActuarialAssurances.Continuous.deathPV, ActuarialAssurances.Continuous.maturityPV]; split_ifs <;> simp_all <;> linarith

