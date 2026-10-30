-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T00:01:17.480845+00:00
-- url     : https://prove2.me/submissions/bf9ed932-949a-4c09-bb7b-27010cb5c325

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ H : SimpleGraph V,
      (∀ ⦃u v : V⦄, K.Adj u v → H.Adj u v) →
      WilliamsonShmoys.HasPlanarDrawingOn H →
      H.edgeSet.ncard ≤ K.edgeSet.ncard) :
    3 * Fintype.card V - 6 ≤ K.edgeSet.ncard := by
  obtain ⟨H, hSub, hH, hEdges⟩ :=
    WilliamsonShmoys.planar_triangulation_extension K hK hV
  rw [← hEdges]
  exact hmax H hSub hH