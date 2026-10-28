-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_bound_for_three_or_more_vertices
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T07:53:20.46934+00:00
-- url     : https://prove2.me/submissions/18ab24f1-c3a7-4108-aea8-73e077d72e5f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Theorems.Thm_WilliamsonShmoys_planar_edge_bound_for_three_or_more_vertices_connect_components
import Theorems.Thm_WilliamsonShmoys_planar_edge_bound_for_three_or_more_vertices_connected_core

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V) :
    L.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨T, hLT, hTConnected, hTPlanar⟩ :=
    WilliamsonShmoys.planar_edge_bound_for_three_or_more_vertices_connect_components
      L hL hCard
  have hTBound :=
    WilliamsonShmoys.planar_edge_bound_for_three_or_more_vertices_connected_core
      T hTPlanar hTConnected hCard
  have hEdgeMono : L.edgeSet.ncard ≤ T.edgeSet.ncard := by
    apply Set.ncard_mono
    exact SimpleGraph.edgeSet_mono hLT
  omega