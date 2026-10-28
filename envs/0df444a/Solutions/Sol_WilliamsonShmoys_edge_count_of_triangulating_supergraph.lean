-- Prove2me | solution 1 for WilliamsonShmoys.edge_count_of_triangulating_supergraph
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T04:11:04.443408+00:00
-- url     : https://prove2.me/submissions/174f0b31-f903-48d7-b67c-a2d45bf3bbc4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_supergraph_of_connected_subgraph

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (J K : SimpleGraph V)
    (hJK : J.edgeSet ⊆ K.edgeSet)
    (hConn : J.Connected)
    (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hMax : ∀ L : SimpleGraph V,
      K.edgeSet ⊆ L.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn L →
      L.edgeSet = K.edgeSet) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨L, hKL, hL, hCount⟩ :=
    WilliamsonShmoys.planar_triangulation_supergraph_of_connected_subgraph
      J K hJK hConn hV hK
  have hEq : L.edgeSet = K.edgeSet := hMax L hKL hL
  simpa [hEq] using hCount