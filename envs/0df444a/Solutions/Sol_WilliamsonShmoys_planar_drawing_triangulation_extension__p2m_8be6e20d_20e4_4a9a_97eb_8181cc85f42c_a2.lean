-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulation_extension__p2m_8be6e20d_20e4_4a9a_97eb_8181cc85f42c_a2
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:31:03.201999+00:00
-- url     : https://prove2.me/submissions/5568980c-a041-4f5f-9c0f-8a3b754fb0e5

import Theorems.Thm_WilliamsonShmoys_exists_planar_edge_count_extension_54a0e51c

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    ∃ M : SimpleGraph V,
      K.edgeSet ⊆ M.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      M.edgeSet.ncard + 6 = 3 * Fintype.card V :=
  WilliamsonShmoys.exists_planar_edge_count_extension_54a0e51c K hK hV
