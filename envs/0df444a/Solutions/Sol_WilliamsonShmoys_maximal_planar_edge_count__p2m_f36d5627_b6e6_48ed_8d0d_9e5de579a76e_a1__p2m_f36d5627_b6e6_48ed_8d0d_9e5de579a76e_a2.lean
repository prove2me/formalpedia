-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_f36d5627_b6e6_48ed_8d0d_9e5de579a76e_a1__p2m_f36d5627_b6e6_48ed_8d0d_9e5de579a76e_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-03T16:33:57.132543+00:00
-- url     : https://prove2.me/submissions/27f6c5de-9c25-4a7e-a69d-82bba54efdbd

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count__p2m_638a1f84_48cf_416d_8d32_57bed5d6bb46_a2
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ (G' : SimpleGraph V), WilliamsonShmoys.HasPlanarDrawingOn G' →
      (∀ u v, H.Adj u v → G'.Adj u v) →
      ∀ u v, G'.Adj u v → H.Adj u v)
    (hn : 3 ≤ Fintype.card V) :
    H.edgeFinset.card = 3 * Fintype.card V - 6 := by
  have hm : ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H := by
    intro K hle hdraw
    apply le_antisymm
    · exact SimpleGraph.le_iff_adj.mpr (hmax K hdraw (SimpleGraph.le_iff_adj.mp hle))
    · exact hle
  have hc :=
    WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_638a1f84_48cf_416d_8d32_57bed5d6bb46_a2
      H hH hn hm
  rw [← H.coe_edgeFinset, Set.ncard_coe_finset] at hc
  exact hc.symm
