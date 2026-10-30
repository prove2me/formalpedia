-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_augmentation__p2m_f4cb8c05_b66d_460b_b025_904e9a860d95_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T19:51:57.582592+00:00
-- url     : https://prove2.me/submissions/1641a8fa-b6df-4c0f-a61d-d3065b06d4ba

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_maximal_completion__p2m_0ce4b12f_9c91_441c_b797_1286dedfdf8a_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_0ce4b12f_9c91_441c_b797_1286dedfdf8a_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hCard : 3 ≤ Fintype.card V)
    (hCount : H.edgeSet.ncard < 3 * Fintype.card V - 6) :
    ∃ K : SimpleGraph V,
      H.edgeSet ⊂ K.edgeSet ∧ WilliamsonShmoys.HasPlanarDrawingOn K := by
  obtain ⟨K, hHK, hK, hmax⟩ :=
    WilliamsonShmoys.planar_maximal_completion__p2m_0ce4b12f_9c91_441c_b797_1286dedfdf8a_a1
      H hH
  have hLower :=
    WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_0ce4b12f_9c91_441c_b797_1286dedfdf8a_a1
      K hK hmax hCard
  have hneq : H.edgeSet ≠ K.edgeSet := by
    intro heq
    have hcardEq : H.edgeSet.ncard = K.edgeSet.ncard := congrArg Set.ncard heq
    omega
  exact ⟨K, Set.ssubset_iff_subset_ne.mpr ⟨hHK, hneq⟩, hK⟩