-- Prove2me | solution 1 for SumOfCubesPractice.cubeSum_eq_triangleSum_sq
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-17T11:07:28.958326+00:00
-- url     : https://prove2.me/submissions/cd700b1e-d2d5-4631-8b75-922eecda439f

import Mathlib
import Definitions.Def_SumOfCubesPractice_triangleSum
import Definitions.Def_SumOfCubesPractice_cubeSum
open SumOfCubesPractice

theorem solution(n : ℕ) :
    cubeSum n = triangleSum n ^ 2 := by
  have htw : ∀ m : ℕ, 2 * triangleSum m = m * (m + 1) := by
    intro m
    induction m with
    | zero => simp [triangleSum]
    | succ m ih =>
      unfold triangleSum at *
      rw [Finset.sum_Icc_succ_top (by omega), mul_add, ih]
      ring
  have hs : ∀ m : ℕ, triangleSum (m + 1) = triangleSum m + (m + 1) := by
    intro m
    unfold triangleSum
    rw [Finset.sum_Icc_succ_top (by omega)]
  induction n with
  | zero => simp [cubeSum, triangleSum]
  | succ n ih =>
    have hc : cubeSum (n + 1) = cubeSum n + (n + 1) ^ 3 := by
      unfold cubeSum
      rw [Finset.sum_Icc_succ_top (by omega)]
    rw [hc, ih, hs n, show (triangleSum n + (n + 1)) ^ 2 = triangleSum n ^ 2 + (n + 1) * (2 * triangleSum n) + (n + 1) ^ 2 by ring, htw n]
    ring
