-- Prove2me | solution 1 for TunnellMap.nearestQuot_tie
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:24:48.611999+00:00
-- url     : https://prove2.me/submissions/73e5c04a-bb08-479a-9eeb-2a63ae7ddb8a

import Definitions.Def_TunnellMap_DeterministicFrame
import Definitions.Def_TunnellMap_ReducedBasisBound
import Definitions.Def_TunnellMap_ResidualTargetTest
import Definitions.Def_TunnellMap_LagrangeGauss

set_option autoImplicit true
open TunnellMap
open OrderedGenerator
namespace TunnellMap
theorem _root_.solution {a b k : ℤ} (ha : 0 < a) (h : 2 * b = (2 * k + 1) * a) :
    nearestQuot b a = if 0 ≤ b then k else k + 1 := by
  have hstep : ∀ m : ℤ, (2 * a * m - 1) / (2 * a) = m - 1 := by
    intro m
    have : 2 * a * m - 1 = (2 * a - 1) + 2 * a * (m - 1) := by ring
    rw [this, Int.add_mul_ediv_left _ _ (by omega : (2 * a : ℤ) ≠ 0),
      Int.ediv_eq_zero_of_lt (by omega) (by omega)]
    omega
  unfold nearestQuot
  by_cases hb : 0 ≤ b
  · rw [if_pos hb, if_pos hb]
    have : 2 * b + a - 1 = 2 * a * (k + 1) - 1 := by linarith
    rw [this, hstep]
    ring
  · rw [if_neg hb, if_neg hb]
    have : -(2 * b) + a - 1 = 2 * a * (-k) - 1 := by linarith
    rw [this, hstep]
    ring
end TunnellMap
