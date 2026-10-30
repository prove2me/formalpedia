-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_bound_connected_induced__p2m_66ade5d4_3842_4532_bbd5_36e43a15d1f5_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:48:34.933984+00:00
-- url     : https://prove2.me/submissions/0e35d426-ec75-4183-8004-2b1c8a1b6a76
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawingOn_induce__p2m_bfb48bad_a912_467d_9a83_873a376cfdde_a1
import Theorems.Thm_WilliamsonShmoys_planar_edge_bound_of_drawing_connected__p2m_bfb48bad_a912_467d_9a83_873a376cfdde_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (s : Finset V)
    (hconn : (H.induce (↑s : Set V)).Connected)
    (hCard : 3 ≤ Fintype.card {v // v ∈ s}) :
    (H.induce (↑s : Set V)).edgeSet.ncard + 6 ≤
      3 * Fintype.card {v // v ∈ s} := by
  exact WilliamsonShmoys.planar_edge_bound_of_drawing_connected__p2m_bfb48bad_a912_467d_9a83_873a376cfdde_a1
    (H.induce (↑s : Set V))
    (WilliamsonShmoys.planar_drawingOn_induce__p2m_bfb48bad_a912_467d_9a83_873a376cfdde_a1 H hH s)
    hconn hCard