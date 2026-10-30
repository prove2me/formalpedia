-- Prove2me | solution 1 for WilliamsonShmoys_planar_edge_bound_of_drawing__p2m_a0822732_7c4f_4d4e_a3ab_e0736d425a71_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T21:48:50.10988+00:00
-- url     : https://prove2.me/submissions/cb6941dd-3d4b-45df-9ca7-b0b67257478b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_extension__p2m_85efdcf1_7002_4c36_9c3f_e040848917fe_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_85efdcf1_7002_4c36_9c3f_e040848917fe_a2
import Theorems.Thm_WilliamsonShmoys_edge_count_mono__p2m_85efdcf1_7002_4c36_9c3f_e040848917fe_a2
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V)
    (hconn : G.Connected) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨H, hGH, hHplanar, hmax, hHconn⟩ :=
    WilliamsonShmoys_maximal_planar_extension__p2m_85efdcf1_7002_4c36_9c3f_e040848917fe_a2
      G hG hconn
  have hHcount :=
    WilliamsonShmoys_maximal_planar_edge_count__p2m_85efdcf1_7002_4c36_9c3f_e040848917fe_a2
      G H hGH hHplanar hmax hV hHconn
  have hmono :=
    WilliamsonShmoys_edge_count_mono__p2m_85efdcf1_7002_4c36_9c3f_e040848917fe_a2
      G H hGH
  omega