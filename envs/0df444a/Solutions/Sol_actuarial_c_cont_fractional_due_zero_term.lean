-- Prove2me | solution 1 for actuarial_c_cont_fractional_due_zero_term
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T14:51:19.024497+00:00
-- url     : https://prove2.me/submissions/945cef4f-2b72-437f-b310-191956410483

import Mathlib
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_cont_fractionalTime
import Definitions.Def_actuarial_c_cont_fractionalDuePV

open ActuarialAssurances.Continuous

open MeasureTheory


theorem solution (m : ℕ) (delta t : ℝ) :
    fractionalDuePV m 0 delta t = 0 := by
  unfold ActuarialAssurances.Continuous.fractionalDuePV  ActuarialAssurances.Continuous.fractionalTime <;> simp <;> ring

