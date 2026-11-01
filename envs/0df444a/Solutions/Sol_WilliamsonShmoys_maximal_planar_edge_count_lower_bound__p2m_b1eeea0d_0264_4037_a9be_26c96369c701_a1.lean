-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_b1eeea0d_0264_4037_a9be_26c96369c701_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:52:30.586359+00:00
-- url     : https://prove2.me/submissions/a2098869-b8b1-4b77-a9a8-78ac538cfb07
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_face_count_certificate__p2m_42928b97_f6a9_47a4_921a_031377856976_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ H : SimpleGraph V, K ≤ H → WilliamsonShmoys.HasPlanarDrawingOn H → H ≤ K) :
    3 * Fintype.card V - 6 ≤ K.edgeSet.ncard := by
  obtain ⟨f, heuler, hfaces⟩ :=
    WilliamsonShmoys.maximal_planar_face_count_certificate__p2m_42928b97_f6a9_47a4_921a_031377856976_a1
      K hcard hK hmax
  omega