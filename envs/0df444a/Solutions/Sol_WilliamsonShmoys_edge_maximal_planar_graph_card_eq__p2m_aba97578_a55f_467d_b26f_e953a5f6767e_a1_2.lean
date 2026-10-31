-- Prove2me | solution 2 for WilliamsonShmoys.edge_maximal_planar_graph_card_eq__p2m_aba97578_a55f_467d_b26f_e953a5f6767e_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:48:10.491623+00:00
-- url     : https://prove2.me/submissions/dbd2f054-2d13-4051-9f0f-f4733c51d738

import Theorems.Thm_WilliamsonShmoys_planar_edge_maximal_graph_edge_count_391f3239_9f51_4455_9b2f_cbbc61103aca

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V) (hH : HasPlanarDrawingOn H)
    (hMax : ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V :=
  WilliamsonShmoys.planar_edge_maximal_graph_edge_count_391f3239_9f51_4455_9b2f_cbbc61103aca H hV hH hMax
