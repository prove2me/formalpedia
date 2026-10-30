-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_le_three_mul_card_sub_six__p2m_c8bd0d06_bddd_4d97_9a5a_50d50f58bad7_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:42:32.435262+00:00
-- url     : https://prove2.me/submissions/ffc3dbe8-aad8-47e1-828b-a749ef79af39
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_completion__p2m_2911e589_9855_41f2_81aa_874f2d2a0dd0_a1
import Theorems.Thm_WilliamsonShmoys_planar_connected_edge_count_bound__p2m_2911e589_9855_41f2_81aa_874f2d2a0dd0_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 ≤ Fintype.card V) :
    L.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨H, hLH, hHplanar, hHconn, hcard⟩ :=
    WilliamsonShmoys.planar_drawing_connected_completion__p2m_2911e589_9855_41f2_81aa_874f2d2a0dd0_a1
      L hplanar hV
  have hbound :=
    WilliamsonShmoys.planar_connected_edge_count_bound__p2m_2911e589_9855_41f2_81aa_874f2d2a0dd0_a1
      H hHplanar hHconn hV
  omega