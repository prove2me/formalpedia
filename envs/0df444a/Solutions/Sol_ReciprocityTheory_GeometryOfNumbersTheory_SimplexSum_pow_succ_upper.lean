-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.SimplexSum.pow_succ_upper
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:00:50.150488+00:00
-- url     : https://prove2.me/submissions/f64ce103-9ed8-46df-8b59-4ab2647a9541

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
    (x + 1) ^ (k + 1) ≤ x ^ (k + 1) + (k + 1) * (x + 1) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h3 : x ^ (k + 1) ≤ (x + 1) ^ (k + 1) := pow_le_pow_left₀ hx (by linarith) _
    rw [show x ^ (k + 1 + 1) = x ^ (k + 1) * x by ring, show (x + 1) ^ (k + 1 + 1) = (x + 1) ^ (k + 1) * (x + 1) by ring]
    rw [show (x + 1) ^ (k + 1) = (x + 1) ^ k * (x + 1) by ring] at ih h3 ⊢
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left ih (by linarith : (0:ℝ) ≤ x + 1)]
end ReciprocityTheory.GeometryOfNumbersTheory.SimplexSum
