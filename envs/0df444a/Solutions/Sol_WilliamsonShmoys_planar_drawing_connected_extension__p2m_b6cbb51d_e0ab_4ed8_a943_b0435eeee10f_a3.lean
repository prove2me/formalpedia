-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_extension__p2m_b6cbb51d_e0ab_4ed8_a943_b0435eeee10f_a3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:46:28.872115+00:00
-- url     : https://prove2.me/submissions/a2056ef1-f946-4110-9d4b-3cecda8edd30
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_extension_from_bridge_step__p2m_b76599c1_0a89_4269_bf03_ff901f7f247a_a2
import Theorems.Thm_WilliamsonShmoys_planar_drawing_bridge_step__p2m_b76599c1_0a89_4269_bf03_ff901f7f247a_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 0 < Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ H : SimpleGraph V, M ≤ H ∧
      (∀ u v, Relation.ReflTransGen H.Adj u v) ∧ WilliamsonShmoys.HasPlanarDrawingOn H := by
  exact WilliamsonShmoys.planar_drawing_connected_extension_from_bridge_step__p2m_b76599c1_0a89_4269_bf03_ff901f7f247a_a2
    hV
    (fun G hG hDisconnected =>
      WilliamsonShmoys.planar_drawing_bridge_step__p2m_b76599c1_0a89_4269_bf03_ff901f7f247a_a2
        G hV hG hDisconnected)
    M hM