-- Prove2me | solution 1 for actuarial_c_cont_fractional_grid_maturity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T14:54:21.865557+00:00
-- url     : https://prove2.me/submissions/c87563fa-e839-417a-bdea-48695d74b28a

import Mathlib
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_cont_fractionalTime

open ActuarialAssurances.Continuous

open MeasureTheory


theorem solution (m n : ℕ) (hm : 0 < m) :
    fractionalTime m (m*n) = (n : ℝ) := by
  unfold fractionalTime
  have : (m : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp

