-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.SimplexSum.S_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:04:18.070818+00:00
-- url     : https://prove2.me/submissions/6517ef82-28d3-4c00-b49d-9cc51c534ad1

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
theorem _root_.solution (i j n : ℕ) : S i (j + 1) n = n * S i j n - S (i + 1) j n := by
  unfold S
  rw [mul_sum, ← sum_sub_distrib]
  apply sum_congr rfl
  intro p hp
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  have : (p.2 : ℝ) = n - p.1 := by rw [← hp]; push_cast; ring
  rw [this]; ring
end ReciprocityTheory.GeometryOfNumbersTheory.SimplexSum
