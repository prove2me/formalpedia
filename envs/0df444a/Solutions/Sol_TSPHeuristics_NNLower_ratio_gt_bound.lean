-- Prove2me | solution 1 for TSPHeuristics.NNLower.ratio_gt_bound
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:09:27.886037+00:00
-- url     : https://prove2.me/submissions/cfce9341-7892-45f3-b5cc-e2697528fc21

import Mathlib
import Definitions.Def_TSPHeuristics_NNLower_LowerBoundFamily

namespace TSPHeuristics.NNLower

theorem aux_rgb_pathLength_closed (i : ℕ) :
    pathLength (i + 1) = (2 / 3) * ((i + 1 : ℕ) : ℝ) * 2 ^ (i + 1) + (8 / 9) * 2 ^ (i + 1)
      + (-1) ^ (i + 1) / 9 - 1 := by
  induction i with
  | zero => norm_num [pathLength]
  | succ k ih =>
    rw [show k + 1 + 1 = k + 2 from rfl, pathLength, ih, ell]
    push_cast
    ring

end TSPHeuristics.NNLower

open TSPHeuristics.NNLower

theorem solution (i : ℕ) (hi : 3 ≤ i) :
    (1 / 3 * Real.logb 2 ((numNodes i : ℝ) + 1) + 4 / 9) * (numNodes i : ℝ) <
      pathLength i + ell i - 1 := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  have hn : ((numNodes (j + 1) : ℕ) : ℝ) = (2 : ℝ) ^ (j + 1 + 1) - 1 := by
    unfold numNodes
    rw [Nat.cast_sub (Nat.one_le_two_pow)]
    push_cast
    ring
  have hlog : Real.logb 2 ((numNodes (j + 1) : ℝ) + 1) = ((j + 1 + 1 : ℕ) : ℝ) := by
    rw [hn, sub_add_cancel, Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
    push_cast
    ring
  rw [hlog, hn, aux_rgb_pathLength_closed, ell]
  have hj : (2 : ℝ) ≤ (j : ℝ) := by
    have : 2 ≤ j := by omega
    exact_mod_cast this
  have hs : ((-1 : ℝ) ^ (j + 1)) ≤ 1 := by
    rcases neg_one_pow_eq_or ℝ (j + 1) with h | h <;> rw [h] <;> norm_num
  push_cast
  have hp : (2 : ℝ) ^ (j + 1 + 1) = 2 * 2 ^ (j + 1) := by ring
  rw [hp]
  nlinarith
