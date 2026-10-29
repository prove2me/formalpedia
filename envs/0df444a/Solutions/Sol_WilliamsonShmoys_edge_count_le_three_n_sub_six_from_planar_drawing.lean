-- Prove2me | solution 1 for WilliamsonShmoys.edge_count_le_three_n_sub_six_from_planar_drawing
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T05:03:24.39155+00:00
-- url     : https://prove2.me/submissions/55d444d6-22e9-40f5-894b-158b3805e4e1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_planar_supergraph_of_drawing__p2m_5438d717_60ba_4719_bd8d_a39b0e45c967_a4
import Theorems.Thm_WilliamsonShmoys_connected_edge_count_le_three_n_sub_six_from_drawing__p2m_5438d717_60ba_4719_bd8d_a39b0e45c967_a4

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hCard : 3 ≤ Fintype.card V) :
    N.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨H, hH, hHConnected, hCount⟩ :=
    WilliamsonShmoys.connected_planar_supergraph_of_drawing__p2m_5438d717_60ba_4719_bd8d_a39b0e45c967_a4
      N hN hCard
  have hBound :=
    WilliamsonShmoys.connected_edge_count_le_three_n_sub_six_from_drawing__p2m_5438d717_60ba_4719_bd8d_a39b0e45c967_a4
      H hH hHConnected hCard
  omega