-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_1bf322db_0dbd_4aed_abd6_bf402bf7bb2f_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T11:39:26.7602+00:00
-- url     : https://prove2.me/submissions/0cc5e2eb-a7c2-478d-adf0-378cd6cd3036
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edgeSet_ncard_le_three_mul_card_sub_six__p2m_b8afd70d_5e18_4708_a739_37d2bdc4e576_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edgeSet_ncard_ge_three_mul_card_sub_six__p2m_b8afd70d_5e18_4708_a739_37d2bdc4e576_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hplanar : HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V,
      K.edgeSet ⊆ L.edgeSet →
      HasPlanarDrawingOn L →
      L.edgeSet = K.edgeSet) :
    K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hupper := WilliamsonShmoys.planar_edgeSet_ncard_le_three_mul_card_sub_six__p2m_b8afd70d_5e18_4708_a739_37d2bdc4e576_a1
    K hcard hplanar
  have hlower := WilliamsonShmoys.maximal_planar_edgeSet_ncard_ge_three_mul_card_sub_six__p2m_b8afd70d_5e18_4708_a739_37d2bdc4e576_a1
    K hcard hplanar hmax
  omega