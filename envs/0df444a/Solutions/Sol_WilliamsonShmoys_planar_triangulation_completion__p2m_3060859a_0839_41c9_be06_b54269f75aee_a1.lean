-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_completion__p2m_3060859a_0839_41c9_be06_b54269f75aee_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:55:30.492416+00:00
-- url     : https://prove2.me/submissions/d3af2a3a-8b03-4d1f-bf95-714a8ce58e5c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_54bfa514_b5d2_470b_aa39_b977e5665440_a1
import Theorems.Thm_WilliamsonShmoys_planar_maximal_edge_count__p2m_54bfa514_b5d2_470b_aa39_b977e5665440_a1

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hPlanar : HasPlanarDrawingOn J) :
    exists N : SimpleGraph V,
      J <= N /\
      HasPlanarDrawingOn N /\
      3 * Fintype.card V - 6 = N.edgeSet.ncard := by
  obtain ⟨N, hJN, hNPlanar, hNmax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_extension__p2m_54bfa514_b5d2_470b_aa39_b977e5665440_a1
      J hV hPlanar
  have hCount :=
    WilliamsonShmoys.planar_maximal_edge_count__p2m_54bfa514_b5d2_470b_aa39_b977e5665440_a1
      N hV hNPlanar hNmax
  exact ⟨N, hJN, hNPlanar, hCount⟩