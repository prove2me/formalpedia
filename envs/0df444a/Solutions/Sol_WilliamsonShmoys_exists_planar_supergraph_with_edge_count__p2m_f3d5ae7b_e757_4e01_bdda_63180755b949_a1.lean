-- Prove2me | solution 1 for WilliamsonShmoys.exists_planar_supergraph_with_edge_count__p2m_f3d5ae7b_e757_4e01_bdda_63180755b949_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T12:31:34.644669+00:00
-- url     : https://prove2.me/submissions/17d1ccc0-735b-4c41-ac03-a2ca8a962fb1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_augmentation__p2m_56ff2e59_7339_4433_a91a_44d558d3726b_a1
import Theorems.Thm_WilliamsonShmoys_planar_completion_from_augmentation__p2m_56ff2e59_7339_4433_a91a_44d558d3726b_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      K.edgeSet ⊆ L.edgeSet ∧
      L.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  apply WilliamsonShmoys.planar_completion_from_augmentation__p2m_56ff2e59_7339_4433_a91a_44d558d3726b_a1 K hK hV
  intro G hG hE
  exact WilliamsonShmoys.planar_edge_augmentation__p2m_56ff2e59_7339_4433_a91a_44d558d3726b_a1 G hG hV hE