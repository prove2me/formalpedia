-- Prove2me | solution 1 for TSPHeuristics.NNLower.pathLength_closed_form
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-27T23:40:29.201561+00:00
-- url     : https://prove2.me/submissions/75d56ccc-4fed-426d-9803-9871e99db32b

import Mathlib
import Definitions.Def_TSPHeuristics_NNLower_LowerBoundFamily

open TSPHeuristics.NNLower

theorem solution (i : ℕ) (hi : 1 ≤ i) :
    pathLength i = (6 * (i : ℝ) * 2 ^ i + 8 * 2 ^ i + (-1) ^ i - 9) / 9 := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  clear hi
  induction j with
  | zero => norm_num [pathLength]
  | succ k ih =>
    have h : pathLength (k + 1 + 1) = 2 * pathLength (k + 1) + 2 * ell (k + 1) := rfl
    rw [h, ih, ell]
    push_cast
    ring
