-- Prove2me | solution 1 for WilliamsonShmoys.exists_triangulation_completion
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T01:13:45.627003+00:00
-- url     : https://prove2.me/submissions/975fb09d-1ff1-498a-9adc-8d78e48e5102
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_supergraph_for_completion
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_count_for_completion

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hLdraw : HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ M : SimpleGraph V, L ≤ M ∧ HasPlanarDrawingOn M ∧
      M.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨M, hLM, hMdraw, hMmax⟩ :=
    WilliamsonShmoys.maximal_drawable_supergraph_for_completion L hLdraw
  exact ⟨M, hLM, hMdraw,
    WilliamsonShmoys.maximal_drawable_edge_count_for_completion
      M hMdraw hCard hMmax⟩