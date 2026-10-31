-- Prove2me | solution 1 for WilliamsonShmoys.planar_simple_graph_edge_upper_bound__p2m_9e9ddd37_2fbe_4f2e_b4a6_63a4b0058d20_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:25:51.055756+00:00
-- url     : https://prove2.me/submissions/960f4a23-ba7b-4f3d-b464-fc1d1c7bb6b2

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_extends_to_maximal_planar__p2m_3eaf26d3_b02e_4c77_b998_3e9af8fb07e7_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V) :
    M.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨H, hSub, _hPlanar, hCount⟩ :=
    WilliamsonShmoys.planar_drawing_extends_to_maximal_planar__p2m_3eaf26d3_b02e_4c77_b998_3e9af8fb07e7_a1
      M hM hCard
  have hEdges : M.edgeSet ⊆ H.edgeSet := hSub
  have hle : M.edgeSet.ncard ≤ H.edgeSet.ncard :=
    Set.ncard_le_ncard hEdges (Set.toFinite H.edgeSet)
  omega