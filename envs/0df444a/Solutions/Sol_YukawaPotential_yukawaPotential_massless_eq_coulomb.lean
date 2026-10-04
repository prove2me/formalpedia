-- Prove2me | solution 1 for YukawaPotential.yukawaPotential_massless_eq_coulomb
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-03T12:55:22.076293+00:00
-- url     : https://prove2.me/submissions/3fb07881-a874-4e0f-81ca-191979e06a70

import Mathlib
import Definitions.Def_YukawaPotential_Defs

open YukawaPotential

theorem solution (g α r : ℝ) :
    yukawaPotential g α 0 r = -g ^ 2 * (1 / r) := by
  unfold yukawaPotential
  simp [mul_zero, zero_mul, neg_zero, Real.exp_zero, mul_one, div_eq_mul_inv, one_div]
