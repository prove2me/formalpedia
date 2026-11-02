-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_drawable_extension__p2m_b4f778a6_f898_4626_8a06_345c4a75a344_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T06:42:26.798192+00:00
-- url     : https://prove2.me/submissions/43f66366-5575-4525-aa4a-e92e0ea685dd

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_drawable_extension_ncard__p2m_f0ae2a89_338a_4b39_88cf_341f6f611f31_a2
import Theorems.Thm_WilliamsonShmoys_ncard_maximal_implies_maximal__p2m_f0ae2a89_338a_4b39_88cf_341f6f611f31_a2
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
        ∀ M : SimpleGraph V, L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M = L := by
  obtain ⟨L, hKL, hL, hmaxK⟩ :=
    WilliamsonShmoys.exists_maximal_drawable_extension_ncard__p2m_f0ae2a89_338a_4b39_88cf_341f6f611f31_a2
      K hcard hK
  refine ⟨L, hKL, hL, ?_⟩
  have hmaxL : ∀ M : SimpleGraph V, L ≤ M →
      WilliamsonShmoys.HasPlanarDrawingOn M → M.edgeSet.ncard ≤ L.edgeSet.ncard := by
    intro M hLM hM
    exact hmaxK M (le_trans hKL hLM) hM
  exact WilliamsonShmoys.ncard_maximal_implies_maximal__p2m_f0ae2a89_338a_4b39_88cf_341f6f611f31_a2
    L hmaxL
