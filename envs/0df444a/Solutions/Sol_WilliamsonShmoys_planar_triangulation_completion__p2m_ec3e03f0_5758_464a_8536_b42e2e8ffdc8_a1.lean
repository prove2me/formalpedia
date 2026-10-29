-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_completion__p2m_ec3e03f0_5758_464a_8536_b42e2e8ffdc8_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T20:42:17.421807+00:00
-- url     : https://prove2.me/submissions/fa9e3f83-e32b-4601-b3e2-cf10a0d665cf
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_drawable_supergraph__p2m_93ac3156_1efb_4b4a_874e_65a14cba6456_a1
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_is_connected__p2m_93ac3156_1efb_4b4a_874e_65a14cba6456_a1
import Theorems.Thm_WilliamsonShmoys_connected_maximal_drawable_edge_count__p2m_93ac3156_1efb_4b4a_874e_65a14cba6456_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hG : HasPlanarDrawingOn G) :
    ∃ P : SimpleGraph V, G ≤ P ∧ HasPlanarDrawingOn P ∧
      P.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨P, hGP, hP, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_drawable_supergraph__p2m_93ac3156_1efb_4b4a_874e_65a14cba6456_a1
      G hG
  have hconn :
      P.Connected :=
    WilliamsonShmoys.maximal_drawable_is_connected__p2m_93ac3156_1efb_4b4a_874e_65a14cba6456_a1
      P hV hP hmax
  exact ⟨P, hGP, hP,
    WilliamsonShmoys.connected_maximal_drawable_edge_count__p2m_93ac3156_1efb_4b4a_874e_65a14cba6456_a1
      P hV hconn hP hmax⟩