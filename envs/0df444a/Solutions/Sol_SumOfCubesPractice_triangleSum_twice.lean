-- Prove2me | solution 1 for SumOfCubesPractice.triangleSum_twice
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-17T11:06:39.700788+00:00
-- url     : https://prove2.me/submissions/3ec6beae-56ba-474a-abe5-3cb03a9f496f

import Mathlib
import Definitions.Def_SumOfCubesPractice_triangleSum
open SumOfCubesPractice

theorem solution(n : ℕ) :
    2 * triangleSum n = n * (n + 1) := by
  induction n with
  | zero => simp [triangleSum]
  | succ n ih =>
    unfold triangleSum at *
    rw [Finset.sum_Icc_succ_top (by omega), mul_add, ih]
    ring
