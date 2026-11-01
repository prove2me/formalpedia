-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_exact_edge_count_completion__p2m_368c0d6c_27a0_4bf2_9016_cc54673fe776_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T22:05:07.551041+00:00
-- url     : https://prove2.me/submissions/bc2900c4-7b78-4a8f-b692-59d5815186be
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_completion__p2m_bcf9fc22_a10c_472d_8ae6_0fdb1da6c723_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_has_exact_edge_count__p2m_bcf9fc22_a10c_472d_8ae6_0fdb1da6c723_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      (∀ u v, K.Adj u v → L.Adj u v) ∧
      3 * Fintype.card V = L.edgeSet.ncard + 6 := by
  obtain ⟨L, hL, hKL, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_has_maximal_completion__p2m_bcf9fc22_a10c_472d_8ae6_0fdb1da6c723_a1
      K hK hcard
  exact ⟨L, hL, hKL,
    WilliamsonShmoys.maximal_planar_drawing_has_exact_edge_count__p2m_bcf9fc22_a10c_472d_8ae6_0fdb1da6c723_a1
      L hL hmax hcard⟩