-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper_bound_afa305d5
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T13:42:59.423864+00:00
-- url     : https://prove2.me/submissions/82b4530d-22ac-4b38-8dc6-7b032847e0ac

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_supergraph_repair_20261028
import Theorems.Thm_WilliamsonShmoys_connected_planar_edge_count_repair_20261028
import Theorems.Thm_WilliamsonShmoys_edgeSet_ncard_mono_repair_20261028

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hCard : 3 <= Fintype.card V) :
    H.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  obtain ⟨K, hHK, hKConnected, hKDraw⟩ :=
    WilliamsonShmoys.planar_drawing_connected_supergraph_repair_20261028 H hDraw hCard
  have hKBound : K.edgeSet.ncard + 6 <= 3 * Fintype.card V :=
    WilliamsonShmoys.connected_planar_edge_count_repair_20261028 K hKConnected hKDraw hCard
  have hEdges : H.edgeSet.ncard <= K.edgeSet.ncard :=
    WilliamsonShmoys.edgeSet_ncard_mono_repair_20261028 H K hHK
  omega