-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_bound__p2m_7b3b301f_ddd2_4d8b_ac03_5e4e874e8368_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:41:22.490602+00:00
-- url     : https://prove2.me/submissions/e1611837-d018-498a-bce9-7a28b7fa0395
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_extension__p2m_b6cbb51d_e0ab_4ed8_a943_b0435eeee10f_a3
import Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound__p2m_b6cbb51d_e0ab_4ed8_a943_b0435eeee10f_a3

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    M.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨H, hMH, hHconn, hHdraw⟩ :=
    WilliamsonShmoys.planar_drawing_connected_extension__p2m_b6cbb51d_e0ab_4ed8_a943_b0435eeee10f_a3
      M (Nat.lt_of_lt_of_le (by decide) hV) hM
  exact WilliamsonShmoys.connected_planar_edge_bound__p2m_b6cbb51d_e0ab_4ed8_a943_b0435eeee10f_a3
    M H hMH hHconn hHdraw hV