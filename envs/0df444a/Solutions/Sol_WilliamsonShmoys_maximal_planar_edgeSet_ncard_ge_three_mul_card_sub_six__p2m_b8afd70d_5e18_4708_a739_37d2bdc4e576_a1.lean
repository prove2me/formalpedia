-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edgeSet_ncard_ge_three_mul_card_sub_six__p2m_b8afd70d_5e18_4708_a739_37d2bdc4e576_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T11:58:11.225994+00:00
-- url     : https://prove2.me/submissions/e3291443-fabd-4100-8e7f-e559c0cfd8d3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_maximal_planar_euler_face_count__p2m_1927a2f2_efe0_4e83_ba03_5beb334dbd6d_a1

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
    3 * Fintype.card V - 6 ≤ K.edgeSet.ncard := by
  obtain ⟨f, heuler, hfaces⟩ :=
    WilliamsonShmoys.maximal_planar_euler_face_count__p2m_1927a2f2_efe0_4e83_ba03_5beb334dbd6d_a1
      K hcard hplanar hmax
  omega