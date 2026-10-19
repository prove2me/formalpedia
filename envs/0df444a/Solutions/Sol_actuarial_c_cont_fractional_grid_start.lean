-- Prove2me | solution 1 for actuarial_c_cont_fractional_grid_start
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T14:51:37.899467+00:00
-- url     : https://prove2.me/submissions/23140f49-41de-4540-8bd8-c54158f541fa

import Mathlib
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_cont_fractionalTime

open ActuarialAssurances.Continuous

open MeasureTheory


theorem solution (m : ℕ) (hm : 0 < m) :
    fractionalTime m 0 = 0 := by
  simp only [ActuarialAssurances.Continuous.fractionalTime]; ring

