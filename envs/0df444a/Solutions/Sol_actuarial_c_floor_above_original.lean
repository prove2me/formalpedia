-- Prove2me | solution 1 for actuarial_c_floor_above_original
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T09:42:34.854402+00:00
-- url     : https://prove2.me/submissions/d5dc9c5f-0bfd-46ed-ad25-750af9b1ebb5

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_floorBenefit

open ActuarialAssurances

theorem solution (f : ℝ) (b : ℕ → ℝ) (j : ℕ) : b j ≤ floorBenefit f b j := by
  simp [floorBenefit]
