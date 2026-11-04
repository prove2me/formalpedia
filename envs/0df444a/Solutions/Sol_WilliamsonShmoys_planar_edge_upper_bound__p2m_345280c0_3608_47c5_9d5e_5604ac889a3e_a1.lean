-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_upper_bound__p2m_345280c0_3608_47c5_9d5e_5604ac889a3e_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T13:05:35.286491+00:00
-- url     : https://prove2.me/submissions/5fa9adef-d0c9-475e-95aa-91ed5a2005a5

import Theorems.Thm_WilliamsonShmoys_planar_drawing_completion__p2m_dbc103f7_2bde_446c_9b3b_46d38358163c_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hH : HasPlanarDrawingOn H) :
    letI : DecidableRel H.Adj := Classical.decRel H.Adj
    H.edgeFinset.card + 6 ≤ 3 * Fintype.card V := by
  classical
  letI : DecidableRel H.Adj := Classical.decRel H.Adj
  obtain ⟨K, hHK, hKplanar, hcard_le, hKcount⟩ :=
    WilliamsonShmoys.planar_drawing_completion__p2m_dbc103f7_2bde_446c_9b3b_46d38358163c_a1 H hV hH
  omega