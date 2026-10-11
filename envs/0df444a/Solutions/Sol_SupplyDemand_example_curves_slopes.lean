-- Prove2me | solution 1 for SupplyDemand.example_curves_slopes
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T18:27:55.22102+00:00
-- url     : https://prove2.me/submissions/a1127f2e-f468-449c-84ee-3f1fed4ffb3a

import Mathlib
import Definitions.Def_SupplyDemand_Model

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open SupplyDemand

theorem solution :
    StrictMono linearSupply ∧ StrictAnti linearDemand ∧
    StrictMonoOn isoelasticSupply (Set.Ioi 0) ∧
    StrictAntiOn isoelasticDemand (Set.Ioi 0) := by
  constructor
  · intro x y hxy
    change 3 * x - 6 < 3 * y - 6
    linarith
  constructor
  · intro x y hxy
    change 32 - 2 * y < 32 - 2 * x
    linarith
  constructor
  · intro x hx y hy hxy
    change 0 < x at hx
    change 5 * x ^ (0.5 : ℝ) < 5 * y ^ (0.5 : ℝ)
    exact mul_lt_mul_of_pos_left
      (Real.rpow_lt_rpow (le_of_lt hx) hxy (by norm_num))
      (by norm_num)
  · intro x hx y hy hxy
    change 0 < x at hx
    change 3 * y ^ (-2 : ℝ) < 3 * x ^ (-2 : ℝ)
    exact mul_lt_mul_of_pos_left
      (Real.rpow_lt_rpow_of_neg hx hxy (by norm_num))
      (by norm_num)
