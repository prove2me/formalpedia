-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawing_has_exact_edge_count_completion__p2m_9a006411_f424_41be_bae2_b9a9d8f6aac6_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:17:18.122454+00:00
-- url     : https://prove2.me/submissions/e9775346-5625-4cf9-84d4-5bde03ce9ead

import Theorems.Thm_WilliamsonShmoys_exists_planar_edge_count_extension_54a0e51c

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      M.edgeSet ⊆ K.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard + 6 = 3 * Fintype.card V :=
  WilliamsonShmoys.exists_planar_edge_count_extension_54a0e51c M hM hV
