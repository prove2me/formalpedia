-- Prove2me | solution 1 for WilliamsonShmoys.triangulated_supergraph_of_connected_drawing
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T04:03:21.688576+00:00
-- url     : https://prove2.me/submissions/4d02b3d4-3e74-48a4-865c-a5c4e56cc6d1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_triangulating_supergraph_of_connected_planar_drawing
import Theorems.Thm_WilliamsonShmoys_edge_count_of_triangulating_supergraph

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
      K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hJK, hK, hMax⟩ :=
    WilliamsonShmoys.triangulating_supergraph_of_connected_planar_drawing J hJ hConn hV
  exact ⟨K, hJK, hK,
    WilliamsonShmoys.edge_count_of_triangulating_supergraph
      J K hJK hConn hV hK hMax⟩