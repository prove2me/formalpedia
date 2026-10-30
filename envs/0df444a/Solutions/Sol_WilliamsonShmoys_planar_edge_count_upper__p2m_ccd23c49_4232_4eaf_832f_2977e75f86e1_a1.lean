-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper__p2m_ccd23c49_4232_4eaf_832f_2977e75f86e1_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:20:35.172849+00:00
-- url     : https://prove2.me/submissions/2f170134-e13e-40df-a024-ae2ae6d250f2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_connected_edge_count_upper__p2m_9f29656c_dc34_4a7a_a3c2_ff1f2fc6d96d_a2
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_of_connected__p2m_9f29656c_dc34_4a7a_a3c2_ff1f2fc6d96d_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V) :
    M.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  have hConnectedBound :
      ∀ {W : Type} [Fintype W] [LinearOrder W] (K : SimpleGraph W),
        HasPlanarDrawingOn K → K.Connected →
        3 ≤ Fintype.card W →
        K.edgeSet.ncard + 6 ≤ 3 * Fintype.card W := by
    intro W instF instL K hK hConn hW
    exact WilliamsonShmoys.planar_connected_edge_count_upper__p2m_9f29656c_dc34_4a7a_a3c2_ff1f2fc6d96d_a2 K hK hConn hW
  exact WilliamsonShmoys.planar_edge_count_upper_of_connected__p2m_9f29656c_dc34_4a7a_a3c2_ff1f2fc6d96d_a2
    M hM hCard hConnectedBound
