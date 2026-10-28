-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_augmentation__p2m_8b750c99_2508_4fa0_8f72_2f809c05bba0_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T19:04:35.621517+00:00
-- url     : https://prove2.me/submissions/6c6db951-0f2d-41ca-bab9-6877b8e9ef5c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_maximal_planar_supergraph__p2m_53ad4955_ddc8_46da_8c61_33a0a25dd9ed_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_bound__p2m_53ad4955_ddc8_46da_8c61_33a0a25dd9ed_a1

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V)
    (hCard : 3 <= Fintype.card V)
    (hR : WilliamsonShmoys.HasPlanarDrawingOn R) :
    ∃ S : SimpleGraph V,
      (∀ u v, R.Adj u v → S.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn S ∧
      3 * Fintype.card V - 6 <= S.edgeSet.ncard := by
  obtain ⟨S, hRS, hS, hMax⟩ :=
    WilliamsonShmoys.finite_maximal_planar_supergraph__p2m_53ad4955_ddc8_46da_8c61_33a0a25dd9ed_a1
      R hR
  exact ⟨S, hRS, hS,
    WilliamsonShmoys.maximal_planar_graph_edge_bound__p2m_53ad4955_ddc8_46da_8c61_33a0a25dd9ed_a1
      S hCard hS hMax⟩