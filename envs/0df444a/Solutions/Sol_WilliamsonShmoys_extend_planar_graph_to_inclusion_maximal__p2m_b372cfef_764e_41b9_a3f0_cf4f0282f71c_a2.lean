-- Prove2me | solution 1 for WilliamsonShmoys_extend_planar_graph_to_inclusion_maximal__p2m_b372cfef_764e_41b9_a3f0_cf4f0282f71c_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T01:40:02.897261+00:00
-- url     : https://prove2.me/submissions/f8cc8e56-3b62-4d31-990a-920551b7bf50

import Theorems.Thm_finite_graph_property_has_maximal_extension__p2m_655608fd_9cc4_4697_9d54_637a0388a99e_a1
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (dG : DecidableRel G.Adj)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    Exists fun (L : SimpleGraph V) => Exists fun (dL : DecidableRel L.Adj) =>
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      G.edgeFinset ⊆ L.edgeFinset ∧
      (∀ (H : SimpleGraph V) (dH : DecidableRel H.Adj),
        WilliamsonShmoys.HasPlanarDrawingOn H →
        L.edgeFinset ⊆ H.edgeFinset → H.edgeFinset = L.edgeFinset) := by
  classical
  obtain ⟨L, hL, hGL, hmax⟩ :=
    finite_graph_property_has_maximal_extension__p2m_655608fd_9cc4_4697_9d54_637a0388a99e_a1
      (P := WilliamsonShmoys.HasPlanarDrawingOn) G hG
  refine ⟨L, Classical.decRel L.Adj, hL, ?_, ?_⟩
  · exact (SimpleGraph.edgeFinset_subset_edgeFinset).2 hGL
  · intro H dH hH hLH
    have hLH' : L ≤ H := (SimpleGraph.edgeFinset_subset_edgeFinset).1 hLH
    have hHL : H ≤ L := hmax H hH hLH'
    exact Finset.Subset.antisymm (SimpleGraph.edgeFinset_mono hHL) hLH