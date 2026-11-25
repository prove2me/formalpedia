-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.E.norm_sq_le_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:03:36.530097+00:00
-- url     : https://prove2.me/submissions/09f220ca-aa9b-4ca3-bf2d-436bbe581410

import Mathlib
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_BasicIdentity_HalfSumNormSubSq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.E
open scoped ComplexConjugate
namespace ReciprocityTheory.L2DbarEstimates.E
theorem _root_.solution (A B : ℂ) (ep : ℝ) (hep : 0 < ep) :
    ‖A‖ ^ 2 ≤ (1 + ep) * ‖A + B‖ ^ 2 + (1 + 1 / ep) * ‖B‖ ^ 2 := by
  have h1 : ‖A‖ ≤ ‖A + B‖ + ‖B‖ := by
    have := norm_sub_le (A + B) B
    simpa using this
  set x := ‖A + B‖ with hx
  set y := ‖B‖ with hy
  set t := 1 / ep with htdef
  have ht : ep * t = 1 := by rw [htdef]; field_simp
  have hx0 : 0 ≤ x := norm_nonneg _
  have hy0 : 0 ≤ y := norm_nonneg _
  have key : 2 * x * y ≤ ep * x ^ 2 + t * y ^ 2 := by
    have h := mul_nonneg hep.le (sq_nonneg (x - t * y))
    have e1 : ep * t * x * y = x * y := by rw [ht]; ring
    have e2 : ep * t * t * y ^ 2 = t * y ^ 2 := by rw [ht]; ring
    nlinarith [h, e1, e2]
  have h2 : ‖A‖ ^ 2 ≤ (x + y) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  nlinarith [h2, key]
end ReciprocityTheory.L2DbarEstimates.E
