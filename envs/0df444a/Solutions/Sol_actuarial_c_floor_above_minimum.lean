-- Prove2me | solution 1 for actuarial_c_floor_above_minimum
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T09:42:34.352153+00:00
-- url     : https://prove2.me/submissions/16456330-5e68-4a77-903f-dec69abba5e5

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_floorBenefit

open ActuarialAssurances

theorem solution (f : ℝ) (b : ℕ → ℝ) (j : ℕ) : f ≤ floorBenefit f b j := by
  simp [floorBenefit]
