-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_bound__p2m_3ca4615a_eebc_4af0_940e_7aeb5834c3ad_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T23:01:47.490533+00:00
-- url     : https://prove2.me/submissions/730245e0-50c6-4931-b470-101cd2b32550

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound__p2m_7d768a9f_2454_410a_aba4_32911cd0fa44_a1
import Theorems.Thm_WilliamsonShmoys_edgeSet_ncard_le_to_edgeFinset_card_le__p2m_90141f6c_e00d_474f_bb06_5b30de1c5624_a1

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hM : HasPlanarDrawingOn M) :
    (letI : DecidableRel M.Adj := Classical.decRel M.Adj
     M.edgeFinset.card ≤ 3 * Fintype.card V - 6) := by
  letI : DecidableRel M.Adj := Classical.decRel M.Adj
  have hbound :
      M.edgeSet.ncard ≤ 3 * Fintype.card V - 6 :=
    WilliamsonShmoys.planar_edge_upper_bound__p2m_7d768a9f_2454_410a_aba4_32911cd0fa44_a1
      M hM hcard
  exact WilliamsonShmoys.edgeSet_ncard_le_to_edgeFinset_card_le__p2m_90141f6c_e00d_474f_bb06_5b30de1c5624_a1
    M (Classical.decRel M.Adj) hbound

