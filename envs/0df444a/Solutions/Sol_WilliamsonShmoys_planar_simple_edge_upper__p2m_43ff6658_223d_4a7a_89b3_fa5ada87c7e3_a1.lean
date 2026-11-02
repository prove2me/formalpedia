-- Prove2me | solution 1 for WilliamsonShmoys.planar_simple_edge_upper__p2m_43ff6658_223d_4a7a_89b3_fa5ada87c7e3_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T11:51:37.003213+00:00
-- url     : https://prove2.me/submissions/8e585328-4ef3-45f4-af25-73472cd8f7c5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_extension__p2m_ad7657d2_129c_4ff8_bf1d_16d96be983d7_a1
import Theorems.Thm_WilliamsonShmoys_connected_planar_edge_upper__p2m_ad7657d2_129c_4ff8_bf1d_16d96be983d7_a1
import Theorems.Thm_WilliamsonShmoys_edgeFinset_card_mono__p2m_ad7657d2_129c_4ff8_bf1d_16d96be983d7_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hH : HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V) :
    H.edgeFinset.card + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨G, hsub, hconn, hdraw⟩ :=
    WilliamsonShmoys.planar_drawing_connected_extension__p2m_ad7657d2_129c_4ff8_bf1d_16d96be983d7_a1 H hH
  letI : DecidableRel G.Adj := Classical.decRel _
  have hconnected :=
    WilliamsonShmoys.connected_planar_edge_upper__p2m_ad7657d2_129c_4ff8_bf1d_16d96be983d7_a1 G hdraw hconn hcard
  have hmono :=
    WilliamsonShmoys.edgeFinset_card_mono__p2m_ad7657d2_129c_4ff8_bf1d_16d96be983d7_a1 H G hsub
  omega