-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.SimplexSum.S_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:04:21.833199+00:00
-- url     : https://prove2.me/submissions/79ffee4b-b31e-4717-b5dc-ba2223f56eab

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
theorem _root_.solution (i n : ℕ) : S i 0 n = ∑ a ∈ range (n + 1), (a : ℝ) ^ i := by
  unfold S
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp
end ReciprocityTheory.GeometryOfNumbersTheory.SimplexSum
