-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_upper_bound__p2m_e972185b_4990_47b3_b33a_686d33f273ec_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T08:14:50.363807+00:00
-- url     : https://prove2.me/submissions/6ee3786c-fad1-45b0-b8ee-bd593a8be059
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_extension__p2m_b05b2ac9_cf86_42cd_81eb_d15df4254060_a1
import Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_edge_bound__p2m_b05b2ac9_cf86_42cd_81eb_d15df4254060_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hH : HasPlanarDrawingOn H) :
    (letI : DecidableRel H.Adj := Classical.decRel H.Adj;
      H.edgeFinset.card + 6 ≤ 3 * Fintype.card V) := by
  classical
  obtain ⟨K, hKdraw, hsub, hcard, hKconn⟩ :=
    WilliamsonShmoys.planar_drawing_connected_extension__p2m_b05b2ac9_cf86_42cd_81eb_d15df4254060_a1
      H hH
  have hKbound :=
    WilliamsonShmoys.connected_planar_drawing_edge_bound__p2m_b05b2ac9_cf86_42cd_81eb_d15df4254060_a1
      K hV hKconn hKdraw
  omega