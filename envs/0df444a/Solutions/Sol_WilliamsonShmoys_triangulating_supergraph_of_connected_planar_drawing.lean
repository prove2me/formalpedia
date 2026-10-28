-- Prove2me | solution 1 for WilliamsonShmoys.triangulating_supergraph_of_connected_planar_drawing
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T04:16:47.87713+00:00
-- url     : https://prove2.me/submissions/888d10a4-5af0-49e8-a87b-53e74e2f46ef

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_edge_maximal_graph_with_property

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hJ : WilliamsonShmoys.HasPlanarDrawingOn J)
    (hConn : J.Connected)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      J.edgeSet ⊆ K.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V,
        K.edgeSet ⊆ L.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn L →
        L.edgeSet = K.edgeSet := by
  exact WilliamsonShmoys.exists_edge_maximal_graph_with_property
    J WilliamsonShmoys.HasPlanarDrawingOn hJ