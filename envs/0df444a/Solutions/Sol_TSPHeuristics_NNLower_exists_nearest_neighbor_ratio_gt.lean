-- Prove2me | solution 1 for TSPHeuristics.NNLower.exists_nearest_neighbor_ratio_gt
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T21:01:02.952994+00:00
-- url     : https://prove2.me/submissions/092d673c-8293-40d5-984d-f6ed70d60b69

import Definitions.Def_TSPHeuristics_NNLower_TSPModel
import Definitions.Def_TSPHeuristics_NNLower_ShortestPathMetric
import Definitions.Def_TSPHeuristics_NNLower_LowerBoundFamily
import Theorems.Thm_TSPHeuristics_NNLower_gbar_isTSPDist
import Theorems.Thm_TSPHeuristics_NNLower_optimal_gbar
import Theorems.Thm_TSPHeuristics_NNLower_gbar_nearest_neighbor_path
import Theorems.Thm_TSPHeuristics_NNLower_ratio_gt_bound
import Theorems.Thm_TSPHeuristics_NNLower_gbar_ratio_exact
import Mathlib

open TSPHeuristics.NNLower

theorem solution (m : ℕ) (hm : 3 < m) :
    ∃ d : Fin (2 ^ m - 1) → Fin (2 ^ m - 1) → ℝ, IsTSPDist d ∧ 0 < optimal d ∧
      ∃ τ : Equiv.Perm (Fin (2 ^ m - 1)), IsNearestNeighborTour d τ ∧
        (1 / 3 * Real.logb 2 (((2 ^ m - 1 : ℕ) : ℝ) + 1) + 4 / 9) * optimal d < tourLength d τ := by
  obtain ⟨i, rfl⟩ : ∃ i, m = i + 1 := ⟨m - 1, by omega⟩
  have hi : 1 ≤ i := by omega
  have hi3 : 3 ≤ i := by omega
  obtain ⟨τ, hτ, hnn⟩ := gbar_nearest_neighbor_path i hi
  have hopt := optimal_gbar i hi
  have hrat := gbar_ratio_exact i hi τ hτ
  have hbound := ratio_gt_bound i hi3
  have hn : ((numNodes i : ℕ) : ℝ) = (2 : ℝ) ^ (i + 1) - 1 := by
    unfold numNodes
    rw [Nat.cast_sub Nat.one_le_two_pow]
    simp
  have h4 : (4 : ℝ) ≤ 2 ^ (i + 1) := by
    calc (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (i + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  refine ⟨gbar i, gbar_isTSPDist i hi, ?_, τ, hnn, ?_⟩
  · show 0 < @optimal (numNodes i) (gbar i)
    rw [hopt]; linarith
  · show (1 / 3 * Real.logb 2 (((2 ^ (i + 1) - 1 : ℕ) : ℝ) + 1) + 4 / 9) *
        @optimal (numNodes i) (gbar i) < @tourLength (numNodes i) (gbar i) τ
    rw [hopt, hrat.1]
    have hb : (1 / 3 * Real.logb 2 (((2 ^ (i + 1) - 1 : ℕ) : ℝ) + 1) + 4 / 9) * (numNodes i : ℝ)
        < pathLength i + ell i - 1 := hbound
    rw [hn] at hb
    exact hb
