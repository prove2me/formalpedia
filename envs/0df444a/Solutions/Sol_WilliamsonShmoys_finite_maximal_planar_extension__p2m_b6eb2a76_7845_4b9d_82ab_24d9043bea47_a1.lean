-- Prove2me | solution 1 for WilliamsonShmoys.finite_maximal_planar_extension__p2m_b6eb2a76_7845_4b9d_82ab_24d9043bea47_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:08:22.343086+00:00
-- url     : https://prove2.me/submissions/19946a21-51af-422f-90fd-29222930dd8a

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_max_edge_planar_extension__p2m_07b78964_cbaf_4bb7_98dc_a4ce7ae0f70a_a1
import Theorems.Thm_WilliamsonShmoys_eq_of_extension_edge_card_bound__p2m_07b78964_cbaf_4bb7_98dc_a4ce7ae0f70a_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ N : SimpleGraph V,
      M ≤ N ∧
      HasPlanarDrawingOn N ∧
      M.edgeSet.ncard ≤ N.edgeSet.ncard ∧
      (∀ K : SimpleGraph V, N ≤ K → HasPlanarDrawingOn K → K = N) := by
  obtain ⟨N, hMN, hNPlanar, hEdges, hMax⟩ :=
    WilliamsonShmoys.exists_max_edge_planar_extension__p2m_07b78964_cbaf_4bb7_98dc_a4ce7ae0f70a_a1
      M hM
  refine ⟨N, hMN, hNPlanar, hEdges, ?_⟩
  intro K hNK hKPlanar
  exact WilliamsonShmoys.eq_of_extension_edge_card_bound__p2m_07b78964_cbaf_4bb7_98dc_a4ce7ae0f70a_a1
    N K hNK (hMax K (le_trans hMN hNK) hKPlanar)
