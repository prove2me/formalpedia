-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_supergraph_edge_ncard__p2m_bd178c5a_f4a2_457a_a392_a201150e58c2_a7
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:35:39.277549+00:00
-- url     : https://prove2.me/submissions/98758b74-33fa-43d7-a33f-8717de448b06

import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_extension__p2m_e750187a_6814_42ad_9805_f7d2cd135631_a2

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

open SimpleGraph

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      L.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      H.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn H :=
  WilliamsonShmoys.planar_drawing_connected_extension__p2m_e750187a_6814_42ad_9805_f7d2cd135631_a2 L hL hV
