-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_extension__p2m_6c2fd8cd_5f03_4713_95f5_290dacd849f4_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:09:04.396072+00:00
-- url     : https://prove2.me/submissions/6f8caeee-2f23-45d4-98c1-1bc9a80fd961

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_maximal_extension_exists__p2m_efe3e864_4fbd_4f0b_a1f2_70ba02623cb8_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_efe3e864_4fbd_4f0b_a1f2_70ba02623cb8_a1
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hN : HasPlanarDrawingOn N)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      N ≤ K ∧ HasPlanarDrawingOn K ∧
        K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hNK, hK, hmax⟩ :=
    WilliamsonShmoys.planar_maximal_extension_exists__p2m_efe3e864_4fbd_4f0b_a1f2_70ba02623cb8_a1 N hN
  exact ⟨K, hNK, hK,
    WilliamsonShmoys.maximal_planar_edge_count__p2m_efe3e864_4fbd_4f0b_a1f2_70ba02623cb8_a1
      K hK hmax hV⟩