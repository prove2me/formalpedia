-- Prove2me | solution 1 for WilliamsonShmoys.triangulation_extension__p2m_67af1d40_5710_49f6_8447_77c85edb00fd_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T03:22:00.241805+00:00
-- url     : https://prove2.me/submissions/2f6dc814-08a0-4fbb-bcb0-f0381786367a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_drawable_maximal_extension__p2m_5d7adedc_405a_4aa7_a840_9d1b809cbdd4_a1
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_count__p2m_5d7adedc_405a_4aa7_a840_9d1b809cbdd4_a1
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V,
      L ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
        (letI : DecidableRel M.Adj := Classical.decRel M.Adj
         M.edgeFinset.card = 3 * Fintype.card V - 6) := by
  obtain ⟨M, hLM, hMdraw, hmax⟩ :=
    WilliamsonShmoys.finite_drawable_maximal_extension__p2m_5d7adedc_405a_4aa7_a840_9d1b809cbdd4_a1
      L hL
  exact ⟨M, hLM, hMdraw,
    WilliamsonShmoys.maximal_drawable_edge_count__p2m_5d7adedc_405a_4aa7_a840_9d1b809cbdd4_a1
      M hcard hMdraw hmax⟩