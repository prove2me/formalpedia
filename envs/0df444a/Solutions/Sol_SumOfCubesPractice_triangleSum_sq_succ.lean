-- Prove2me | solution 1 for SumOfCubesPractice.triangleSum_sq_succ
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-17T11:06:54.067985+00:00
-- url     : https://prove2.me/submissions/2cfff54a-9e06-4185-8f98-bfeecac28d96

import Mathlib
import Definitions.Def_SumOfCubesPractice_triangleSum
open SumOfCubesPractice

theorem solution(n : ℕ) :
    triangleSum (n + 1) ^ 2 = triangleSum n ^ 2 + (n + 1) ^ 3 := by
  have htw : ∀ m : ℕ, 2 * triangleSum m = m * (m + 1) := by
    intro m
    induction m with
    | zero => simp [triangleSum]
    | succ m ih =>
      unfold triangleSum at *
      rw [Finset.sum_Icc_succ_top (by omega), mul_add, ih]
      ring
  have hs : triangleSum (n + 1) = triangleSum n + (n + 1) := by
    unfold triangleSum
    rw [Finset.sum_Icc_succ_top (by omega)]
  rw [hs, show (triangleSum n + (n + 1)) ^ 2 = triangleSum n ^ 2 + (n + 1) * (2 * triangleSum n) + (n + 1) ^ 2 by ring, htw n]
  ring
