-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_edge_upper_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T00:17:55.931284+00:00
-- url     : https://prove2.me/submissions/b7a7e851-3c0c-4ac4-a446-b51c5e2968b2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Theorems.Thm_WilliamsonShmoys_connected_planar_edge_upper_bound_finite_maximal_extension
import Theorems.Thm_WilliamsonShmoys_connected_planar_edge_upper_bound_maximal_drawing_core

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hconn : H.Connected)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    H.edgeSet.ncard <= 3 * Fintype.card V - 6 := by
  obtain ⟨K, hHK, hKplanar, hKmax, hcard⟩ :=
    WilliamsonShmoys.connected_planar_edge_upper_bound_finite_maximal_extension H hH
  have hbound :=
    WilliamsonShmoys.connected_planar_edge_upper_bound_maximal_drawing_core K hV hKplanar hKmax
  exact hcard.trans hbound