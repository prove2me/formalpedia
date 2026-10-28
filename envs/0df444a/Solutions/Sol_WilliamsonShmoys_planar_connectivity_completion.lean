-- Prove2me | solution 1 for WilliamsonShmoys.planar_connectivity_completion
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T08:55:05.067379+00:00
-- url     : https://prove2.me/submissions/553c97c4-97ba-4aef-91be-d16f2b056b28
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_connected_supergraph_three_vertices

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hP : WilliamsonShmoys.HasPlanarDrawingOn P) :
    ∃ Q : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn Q ∧
      Q.Connected ∧
      P.edgeSet.ncard ≤ Q.edgeSet.ncard := by
  obtain ⟨Q, hQ, hConnected, _hSubgraph, hEdgeCount⟩ :=
    WilliamsonShmoys.planar_connected_supergraph_three_vertices P hCard hP
  exact ⟨Q, hQ, hConnected, hEdgeCount⟩