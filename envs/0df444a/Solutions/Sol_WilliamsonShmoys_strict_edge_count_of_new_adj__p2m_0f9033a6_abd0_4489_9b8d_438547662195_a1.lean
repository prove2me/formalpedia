-- Prove2me | solution 1 for WilliamsonShmoys.strict_edge_count_of_new_adj__p2m_0f9033a6_abd0_4489_9b8d_438547662195_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:02:51.828609+00:00
-- url     : https://prove2.me/submissions/78496b1d-eb49-444f-a27e-c5a97c8ba410

import Mathlib

/-- Adding a new adjacency to a finite simple graph strictly increases its edge count. -/
theorem solution {V : Type} [Fintype V] [DecidableEq V]
    (K L : SimpleGraph V) (hKL : K ≤ L) (u v : V) (hL : L.Adj u v)
    (hK : ¬ K.Adj u v) : K.edgeSet.ncard < L.edgeSet.ncard := by
  apply Set.ncard_lt_ncard
  · refine Set.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
    · exact SimpleGraph.edgeSet_subset_edgeSet.mpr hKL
    · intro hEq
      have hmem : s(u, v) ∈ L.edgeSet := by simpa using hL
      have hmemK : s(u, v) ∈ K.edgeSet := hEq ▸ hmem
      exact hK (by simpa using hmemK)
  · exact Set.toFinite _