-- Prove2me | solution 1 for SPFacilityGraph.MetricGraph.dist_comm
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-26T23:13:31.490574+00:00
-- url     : https://prove2.me/submissions/714dd2fd-08f6-4963-bdcf-3a333516954a

import Mathlib
import Theorems.Thm_SPFacilityGraph_MetricGraph_dist_le_walk
import Theorems.Thm_SPFacilityGraph_MetricGraph_exists_walk_eq_dist

set_option autoImplicit false

open SPFacilityGraph

lemma SPFacilityGraph.MetricGraph.dist_comm_le {k : ℕ} (G : MetricGraph k) (x y : G.Pt) :
    G.dist y x ≤ G.dist x y := by
  obtain ⟨m, p, h0, hm, hw, hL⟩ := G.exists_walk_eq_dist x y
  rw [← hL]
  have h := G.dist_le_walk y x m (fun j => p (m - j)) (by simpa using hm) (by simpa using h0) ?_
  · refine h.trans (le_of_eq ?_)
    rw [← Finset.sum_range_reflect]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    rw [norm_sub_rev]
    congr 2 <;> congr 1 <;> omega
  · intro j hj
    obtain ⟨e, he, h1, h2⟩ := hw (m - j - 1) (by omega)
    refine ⟨e, he, ?_, ?_⟩
    · show p (m - j) ∈ _
      rwa [show m - j - 1 + 1 = m - j by omega] at h2
    · show p (m - (j + 1)) ∈ _
      rwa [show m - j - 1 = m - (j + 1) by omega] at h1

theorem solution {k : ℕ} (G : MetricGraph k) (x y : G.Pt) :
    G.dist x y = G.dist y x :=
  le_antisymm (G.dist_comm_le y x) (G.dist_comm_le x y)
