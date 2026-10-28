-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_supergraph_completion_task_2f486b23_4a17_4b27_89f1_8ee712518760
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T21:08:42.773558+00:00
-- url     : https://prove2.me/submissions/8e0fff41-5220-40af-bc95-3ffa98b191cc

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_maximal_supergraph_task_2f486b23_4a17_4b27_89f1_8ee712518760

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      (∀ M : SimpleGraph V, L ≤ M →
        WilliamsonShmoys.HasPlanarDrawingOn M → M = L) := by
  obtain ⟨L, hKL, hPL, hmax⟩ :=
    WilliamsonShmoys.finite_maximal_supergraph_task_2f486b23_4a17_4b27_89f1_8ee712518760
      K WilliamsonShmoys.HasPlanarDrawingOn hK
  exact ⟨L, hKL, hPL, fun M hLM hPM => hmax M hLM hPM⟩