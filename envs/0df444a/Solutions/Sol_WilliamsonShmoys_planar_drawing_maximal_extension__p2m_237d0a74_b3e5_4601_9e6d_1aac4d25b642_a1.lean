-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_extension__p2m_237d0a74_b3e5_4601_9e6d_1aac4d25b642_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:35:42.043823+00:00
-- url     : https://prove2.me/submissions/a168cf89-c4d4-4d37-958e-7c64cd41e4a3

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_finite_exists_max_predicate__p2m_caf8a86e_ba48_4365_a372_a27064dc0c60_a1
import Theorems.Thm_finite_simpleGraph_of_fintype__p2m_caf8a86e_ba48_4365_a372_a27064dc0c60_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      ∀ M : SimpleGraph V,
        L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M →
        M.edgeSet.ncard ≤ L.edgeSet.ncard := by
  letI : Finite (SimpleGraph V) := finite_simpleGraph_of_fintype__p2m_caf8a86e_ba48_4365_a372_a27064dc0c60_a1
  obtain ⟨L, hL, hmax⟩ := finite_exists_max_predicate__p2m_caf8a86e_ba48_4365_a372_a27064dc0c60_a1
    (P := fun G : SimpleGraph V => K ≤ G ∧ WilliamsonShmoys.HasPlanarDrawingOn G)
    (f := fun G : SimpleGraph V => G.edgeSet.ncard)
    ⟨K, le_rfl, hplanar⟩
  exact ⟨L, hL.1, hL.2, fun M hLM hMplanar =>
    hmax M ⟨le_trans hL.1 hLM, hMplanar⟩⟩