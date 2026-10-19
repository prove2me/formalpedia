-- Prove2me | solution 1 for actuarial_c_cont_zero_interest_continuous_annuity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T14:52:17.332507+00:00
-- url     : https://prove2.me/submissions/79a54e49-dbf6-40d3-914b-eb001932918d

import Mathlib
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_cont_exposure
import Definitions.Def_actuarial_c_cont_continuousAnnuityPV

open ActuarialAssurances.Continuous

open MeasureTheory


theorem solution (n t : ℝ) :
    continuousAnnuityPV n 0 t = exposure n t := by
  unfold ActuarialAssurances.Continuous.continuousAnnuityPV  ActuarialAssurances.Continuous.exposure <;> simp <;> ring

