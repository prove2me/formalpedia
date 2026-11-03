-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulation_extension__p2m_1508a319_0bdf_43a6_9c8f_5ec7d4360d47_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T15:49:46.585118+00:00
-- url     : https://prove2.me/submissions/2e97163b-fead-4ff0-8cf4-018360e8ffc6

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_maximal_planar_extension__p2m_f922730b_ca22_4588_ba9a_35deaa5a3fb1_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_f922730b_ca22_4588_ba9a_35deaa5a3fb1_a1

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G)
    (hn : 3 <= Fintype.card V) :
    Exists fun H : SimpleGraph V =>
      G <= H /\ HasPlanarDrawingOn H /\
        (letI : DecidableRel H.Adj := Classical.decRel _
         H.edgeFinset.card = 3 * Fintype.card V - 6) := by
  classical
  obtain ⟨H, hGH, hH, hmax⟩ :=
    WilliamsonShmoys.maximal_planar_extension__p2m_f922730b_ca22_4588_ba9a_35deaa5a3fb1_a1
      G hG
  refine ⟨H, hGH, hH, ?_⟩
  exact WilliamsonShmoys.maximal_planar_edge_count__p2m_f922730b_ca22_4588_ba9a_35deaa5a3fb1_a1
    H hH hn hmax