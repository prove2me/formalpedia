-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawable_maximal_supergraph__p2m_e31b05a7_4e78_4789_8a19_ecdeedbcdfa7_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T03:19:38.246095+00:00
-- url     : https://prove2.me/submissions/00e5bbd4-5e16-4f12-9ff9-5a6d53d3bdc2

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_nonempty_subset_has_maximal__p2m_350700c7_dd24_47f5_9bef_0db864652b8b_a3
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V,
      M ≤ N ∧ WilliamsonShmoys.HasPlanarDrawingOn N ∧
        ∀ P : SimpleGraph V, N ≤ P → WilliamsonShmoys.HasPlanarDrawingOn P → P = N := by
  classical
  let S : Set (SimpleGraph V) :=
    {N | M ≤ N ∧ WilliamsonShmoys.HasPlanarDrawingOn N}
  have hS : S.Nonempty := ⟨M, le_rfl, hM⟩
  obtain ⟨N, hN, hmax⟩ :=
    WilliamsonShmoys.finite_nonempty_subset_has_maximal__p2m_350700c7_dd24_47f5_9bef_0db864652b8b_a3
      S hS
  refine ⟨N, hN.1, hN.2, ?_⟩
  intro P hNP hP
  apply hmax P ?_ hNP
  exact ⟨le_trans hN.1 hNP, hP⟩