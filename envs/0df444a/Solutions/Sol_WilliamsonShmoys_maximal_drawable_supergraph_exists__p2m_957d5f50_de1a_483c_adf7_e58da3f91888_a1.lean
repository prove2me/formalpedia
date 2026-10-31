-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_supergraph_exists__p2m_957d5f50_de1a_483c_adf7_e58da3f91888_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:29:20.233509+00:00
-- url     : https://prove2.me/submissions/85041804-e3ad-45f5-8af2-8357dda6a5bf

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_poset_has_maximal__p2m_d962869e_258d_4947_a612_83f18b157228_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : HasPlanarDrawingOn K) :
    ∃ M : SimpleGraph V, K ≤ M ∧ HasPlanarDrawingOn M ∧
      ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N ≤ M := by
  let S : SimpleGraph V → Prop := fun G => K ≤ G ∧ HasPlanarDrawingOn G
  obtain ⟨M, hM, hMax⟩ :=
    WilliamsonShmoys.finite_poset_has_maximal__p2m_d962869e_258d_4947_a612_83f18b157228_a1
      (α := SimpleGraph V) S ⟨K, le_rfl, hK⟩
  refine ⟨M, hM.1, hM.2, ?_⟩
  intro N hMN hN
  apply hMax N
  · exact ⟨le_trans hM.1 hMN, hN⟩
  · exact hMN