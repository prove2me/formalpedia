-- Prove2me | solution 1 for WilliamsonShmoys.drawable_triangulation_extension
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T00:18:14.357573+00:00
-- url     : https://prove2.me/submissions/a24de721-c374-456b-a93a-a8bd6f6b9281
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawable_maximal_extension_037368dd_04cc_4345_b537_96bdbb1ae146
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_count_037368dd_04cc_4345_b537_96bdbb1ae146

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (X : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn X)
    (hV : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      X ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      X.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨H, hXH, hDrawH, hCount, hMax⟩ :=
    WilliamsonShmoys.drawable_maximal_extension_037368dd_04cc_4345_b537_96bdbb1ae146 X hdraw
  refine ⟨H, hXH, hDrawH, hCount, ?_⟩
  exact WilliamsonShmoys.maximal_drawable_edge_count_037368dd_04cc_4345_b537_96bdbb1ae146
    H hV hDrawH hMax
