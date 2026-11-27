-- Prove2me | solution 1 for SPFacilityGraph.MetricGraph.dist_triangle
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-26T23:13:31.995699+00:00
-- url     : https://prove2.me/submissions/a2c30eb5-5d2c-4dd9-b6b0-f771583ce7bb

import Mathlib
import Theorems.Thm_SPFacilityGraph_MetricGraph_dist_le_walk
import Theorems.Thm_SPFacilityGraph_MetricGraph_exists_walk_eq_dist

set_option autoImplicit false

open SPFacilityGraph

theorem solution {k : ℕ} (G : MetricGraph k) (x y z : G.Pt) :
    G.dist x z ≤ G.dist x y + G.dist y z := by
  obtain ⟨m, p, hp0, hpm, hpw, hpL⟩ := G.exists_walk_eq_dist x y
  obtain ⟨n, q, hq0, hqn, hqw, hqL⟩ := G.exists_walk_eq_dist y z
  have hpq : p m = q 0 := hpm.trans hq0.symm
  let r : ℕ → EuclideanSpace ℝ (Fin k) := fun j => if j ≤ m then p j else q (j - m)
  have h := G.dist_le_walk x z (m + n) r (by simp [r, hp0]) ?_ ?_
  · refine h.trans (le_of_eq ?_)
    rw [← hpL, ← hqL, Finset.sum_range_add]
    congr 1
    · apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mem_range] at hj
      simp [r, show j ≤ m by omega, show j + 1 ≤ m by omega]
    · apply Finset.sum_congr rfl
      intro j _
      by_cases h : j = 0
      · subst h; simp [r, hpq]
      · simp [r, show ¬ m + j ≤ m by omega, show ¬ m + j + 1 ≤ m by omega,
          show m + j + 1 - m = j + 1 by omega]
  · by_cases h : n = 0
    · subst h; simp [r, hpm, ← hq0, hqn]
    · simp [r, show ¬ m + n ≤ m by omega, hqn]
  · intro j hj
    by_cases h : j + 1 ≤ m
    · have := hpw j (by omega)
      simpa [r, h, show j ≤ m by omega] using this
    · by_cases h' : j = m
      · have := hqw 0 (by omega)
        simpa [r, h', hpq, show j + 1 - j = 1 by omega] using this
      · have := hqw (j - m) (by omega)
        simpa [r, show ¬ j ≤ m by omega, h, show j + 1 - m = j - m + 1 by omega] using this
