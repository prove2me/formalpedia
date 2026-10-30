-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_augmentation__p2m_56ff2e59_7339_4433_a91a_44d558d3726b_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T12:49:06.947856+00:00
-- url     : https://prove2.me/submissions/0dc1fbcf-e3d4-4c27-8dc3-a7616bf55226
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_augmentation_triangulation__p2m_e279d529_0df7_4422_b7c0_ab730b7394ba_a1
import Theorems.Thm_WilliamsonShmoys_planar_edge_augmentation_extend_planar__p2m_e279d529_0df7_4422_b7c0_ab730b7394ba_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V)
    (hE : K.edgeSet.ncard + 6 < 3 * Fintype.card V) :
    ∃ L : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      K.edgeSet ⊆ L.edgeSet ∧
      L.edgeSet.ncard = K.edgeSet.ncard + 1 := by
  obtain ⟨T, hT, hKT, hTcard⟩ :=
    WilliamsonShmoys.planar_edge_augmentation_triangulation__p2m_e279d529_0df7_4422_b7c0_ab730b7394ba_a1
      K hK hV hE
  exact WilliamsonShmoys.planar_edge_augmentation_extend_planar__p2m_e279d529_0df7_4422_b7c0_ab730b7394ba_a2
    K T hT hKT hE hTcard