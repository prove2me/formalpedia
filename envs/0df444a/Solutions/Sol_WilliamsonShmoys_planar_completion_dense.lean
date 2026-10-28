-- Prove2me | solution 1 for WilliamsonShmoys.planar_completion_dense
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T12:32:53.631608+00:00
-- url     : https://prove2.me/submissions/93bb2380-13e6-4f4a-9c4c-69ac4cc75382
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_completion_exists_maximal_extension
import Theorems.Thm_WilliamsonShmoys_completion_maximal_drawable_edge_bound

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hdraw : HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V, L ≤ M ∧ HasPlanarDrawingOn M ∧
      3 * Fintype.card V - 6 ≤ M.edgeSet.ncard := by
  obtain ⟨M, hLM, hMdraw, hMmax⟩ :=
    WilliamsonShmoys.planar_completion_exists_maximal_extension L hdraw
  exact ⟨M, hLM, hMdraw,
    WilliamsonShmoys.completion_maximal_drawable_edge_bound M hV hMdraw hMmax⟩