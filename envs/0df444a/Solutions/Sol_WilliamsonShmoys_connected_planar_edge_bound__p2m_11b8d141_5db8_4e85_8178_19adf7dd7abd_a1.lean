-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_edge_bound__p2m_11b8d141_5db8_4e85_8178_19adf7dd7abd_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T12:40:50.473648+00:00
-- url     : https://prove2.me/submissions/a78be7eb-252d-49a3-9577-a306fbabe3d8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension_connected__p2m_ea761ab7_f54e_41d1_973a_d18cf519585a_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_ea761ab7_f54e_41d1_973a_d18cf519585a_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hconn : H.Connected)
    (hV : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨K, hsub, hK, hKconn, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_extension_connected__p2m_ea761ab7_f54e_41d1_973a_d18cf519585a_a1
      H hH hconn
  have hcount :=
    WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_ea761ab7_f54e_41d1_973a_d18cf519585a_a1
      K hK hV hKconn hmax
  have hsubcard : H.edgeSet.ncard ≤ K.edgeSet.ncard := Set.ncard_mono hsub
  omega