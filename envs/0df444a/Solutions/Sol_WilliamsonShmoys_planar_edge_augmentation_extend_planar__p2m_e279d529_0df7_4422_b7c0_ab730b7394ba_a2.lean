-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_augmentation_extend_planar__p2m_e279d529_0df7_4422_b7c0_ab730b7394ba_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T13:16:16.360987+00:00
-- url     : https://prove2.me/submissions/ad72842f-9bf9-47ef-a709-4e5d3e4e3ad4

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planarDrawingOn_of_edgeSet_subset__p2m_f10e52ed_7e34_4f15_bfd4_3ce6b850e38c_a2
import Theorems.Thm_WilliamsonShmoys_add_one_edge_subgraph__p2m_f10e52ed_7e34_4f15_bfd4_3ce6b850e38c_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K T : SimpleGraph V)
    (hT : WilliamsonShmoys.HasPlanarDrawingOn T)
    (hKT : K.edgeSet ⊆ T.edgeSet)
    (hE : K.edgeSet.ncard + 6 < 3 * Fintype.card V)
    (hTcard : T.edgeSet.ncard = 3 * Fintype.card V - 6) :
    ∃ L : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      K.edgeSet ⊆ L.edgeSet ∧
      L.edgeSet.ncard = K.edgeSet.ncard + 1 := by
  obtain ⟨L, hKL, hLT, hLcard⟩ :=
    WilliamsonShmoys.add_one_edge_subgraph__p2m_f10e52ed_7e34_4f15_bfd4_3ce6b850e38c_a2
      K T hKT hE hTcard
  exact ⟨L,
    WilliamsonShmoys.planarDrawingOn_of_edgeSet_subset__p2m_f10e52ed_7e34_4f15_bfd4_3ce6b850e38c_a2
      hT hLT,
    hKL, hLcard⟩