-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_augmentation_triangulation__p2m_e279d529_0df7_4422_b7c0_ab730b7394ba_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T13:04:41.024001+00:00
-- url     : https://prove2.me/submissions/96844a72-2635-4c20-9d01-32232c851684
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_extension_maximal__p2m_21bb6f97_2922_436c_8d92_71f0b7399afd_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_21bb6f97_2922_436c_8d92_71f0b7399afd_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V)
    (hE : K.edgeSet.ncard + 6 < 3 * Fintype.card V) :
    ∃ T : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn T ∧
      K.edgeSet ⊆ T.edgeSet ∧
      T.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨T, hT, hKT, hmax⟩ :=
    WilliamsonShmoys.planar_extension_maximal__p2m_21bb6f97_2922_436c_8d92_71f0b7399afd_a1 K hK
  have hcard := WilliamsonShmoys.maximal_planar_edge_count__p2m_21bb6f97_2922_436c_8d92_71f0b7399afd_a1 T hT hmax hV
  exact ⟨T, hT, hKT, hcard⟩