-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.SimplexSum.pow_succ_lower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:00:44.688834+00:00
-- url     : https://prove2.me/submissions/448f9b13-a23b-4fff-8793-56824a7349d7

import Mathlib
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_AsymptoticSequences_SimplexSumSt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open Filter Asymptotics Finset
open ReciprocityTheory.GeometryOfNumbersTheory.SimplexSum
namespace ReciprocityTheory.GeometryOfNumbersTheory.SimplexSum
theorem _root_.solution (x : ℝ) (hx : 0 ≤ x) (k : ℕ) :
    x ^ (k + 1) + (k + 1) * x ^ k ≤ (x + 1) ^ (k + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 : 0 ≤ x ^ k := pow_nonneg hx k
    have h2 : 0 ≤ (k : ℝ) + 1 := by positivity
    rw [show x ^ (k + 1 + 1) = x ^ k * x * x by ring, show (x + 1) ^ (k + 1 + 1) = (x + 1) ^ (k + 1) * (x + 1) by ring,
      show x ^ (k + 1) = x ^ k * x by ring]
    rw [show x ^ (k + 1) = x ^ k * x by ring] at ih
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left ih (by linarith : (0:ℝ) ≤ x + 1), mul_nonneg h2 h1]
end ReciprocityTheory.GeometryOfNumbersTheory.SimplexSum
