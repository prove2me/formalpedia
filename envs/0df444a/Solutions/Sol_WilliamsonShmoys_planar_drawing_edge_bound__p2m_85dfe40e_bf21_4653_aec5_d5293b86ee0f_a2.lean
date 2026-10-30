-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_bound__p2m_85dfe40e_bf21_4653_aec5_d5293b86ee0f_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T21:49:30.136625+00:00
-- url     : https://prove2.me/submissions/f3471748-0ab1-426e-a251-0ffa3981f99e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_7b8c7f37_b8de_44ac_bf27_503e942d415a_a3
import Theorems.Thm_WilliamsonShmoys_edge_count_maximal_planar__p2m_7b8c7f37_b8de_44ac_bf27_503e942d415a_a3
import Mathlib.Tactic

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨H, hGH, hH, hMax, hCard⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_extension__p2m_7b8c7f37_b8de_44ac_bf27_503e942d415a_a3 G hG hV
  have hExact :=
    WilliamsonShmoys.edge_count_maximal_planar__p2m_7b8c7f37_b8de_44ac_bf27_503e942d415a_a3 H hH hV hMax
  omega