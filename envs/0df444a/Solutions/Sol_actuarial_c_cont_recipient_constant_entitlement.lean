-- Prove2me | solution 1 for actuarial_c_cont_recipient_constant_entitlement
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T14:51:57.131484+00:00
-- url     : https://prove2.me/submissions/11ac06bc-890f-46e4-bedf-85108df6c7ba

import Mathlib
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_cont_deathPV
import Definitions.Def_actuarial_c_cont_recipientDeathPV

open ActuarialAssurances.Continuous

open MeasureTheory


theorem solution (n delta t c : ℝ) :
    recipientDeathPV n delta t (fun _ => c) =
      c * deathPV n delta t := by
  simp [ActuarialAssurances.Continuous.deathPV, ActuarialAssurances.Continuous.recipientDeathPV]

