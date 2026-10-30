-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper_c4011bda_e2a2_4391_a47d_b4ea4febecd9
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T06:28:48.808888+00:00
-- url     : https://prove2.me/submissions/e67c57e6-1519-431c-a9db-ca0eefd4aded
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_supergraph_for_edge_count_c4011bda_e2a2_4391_a47d_b4ea4febecd9
import Theorems.Thm_WilliamsonShmoys_connected_planar_edge_count_for_edge_count_c4011bda_e2a2_4391_a47d_b4ea4febecd9
set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : HasPlanarDrawingOn L)
    (hCard : 3 <= Fintype.card V) :
    L.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  obtain ⟨H, hLH, hConnected, hPlanar⟩ :=
    WilliamsonShmoys.planar_drawing_connected_supergraph_for_edge_count_c4011bda_e2a2_4391_a47d_b4ea4febecd9
      L hL hCard
  have hBound :=
    WilliamsonShmoys.connected_planar_edge_count_for_edge_count_c4011bda_e2a2_4391_a47d_b4ea4febecd9
      H hPlanar hConnected hCard
  have hEdges : L.edgeSet.ncard <= H.edgeSet.ncard :=
    Set.ncard_mono (SimpleGraph.edgeSet_mono hLH)
  omega