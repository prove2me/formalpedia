-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.SimplexSum.sum_bounds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:12:33.074781+00:00
-- url     : https://prove2.me/submissions/2fbad281-362c-453d-886b-e0dab5202738

import Mathlib
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_AsymptoticSequences_SimplexSumSt
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_SimplexSum_pow_succ_lower
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_SimplexSum_pow_succ_upper

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
theorem _root_.solution (k n : ℕ) :
    (n : ℝ) ^ (k + 1) ≤ (k + 1) * ∑ a ∈ range (n + 1), (a : ℝ) ^ k ∧
      (k + 1) * ∑ a ∈ range (n + 1), (a : ℝ) ^ k ≤ (n : ℝ) ^ (k + 1) + (k + 1) * (n : ℝ) ^ k := by
  induction n with
  | zero =>
    simp only [zero_add, range_one, sum_singleton, Nat.cast_zero]
    constructor
    · rw [pow_succ, mul_zero]; positivity
    · rw [pow_succ, mul_zero, zero_add]
  | succ n ih =>
    obtain ⟨ih1, ih2⟩ := ih
    rw [sum_range_succ]
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hl := pow_succ_lower (n : ℝ) hn k
    have hu := pow_succ_upper (n : ℝ) hn k
    push_cast
    constructor <;> nlinarith
end ReciprocityTheory.GeometryOfNumbersTheory.SimplexSum
