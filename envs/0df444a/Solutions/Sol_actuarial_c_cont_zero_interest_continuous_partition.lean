-- Prove2me | solution 1 for actuarial_c_cont_zero_interest_continuous_partition
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T14:52:41.175298+00:00
-- url     : https://prove2.me/submissions/175d12c5-7805-4808-ab4f-6cb1101148e0

import Mathlib
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_cont_deathPV
import Definitions.Def_actuarial_c_cont_maturityPV

open ActuarialAssurances.Continuous

open MeasureTheory


theorem solution (n t : ℝ)
    (hn : 0 ≤ n) (ht : 0 ≤ t) :
    deathPV n 0 t + maturityPV n 0 t = 1 := by
  simp only [ActuarialAssurances.Continuous.deathPV, ActuarialAssurances.Continuous.maturityPV]; split_ifs <;> simp_all <;> linarith

