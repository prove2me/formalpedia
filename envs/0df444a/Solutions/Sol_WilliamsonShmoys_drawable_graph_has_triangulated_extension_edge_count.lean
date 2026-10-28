-- Prove2me | solution 1 for WilliamsonShmoys.drawable_graph_has_triangulated_extension_edge_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T21:42:43.182657+00:00
-- url     : https://prove2.me/submissions/66a4d476-6258-4f27-b124-7dad8145ad66
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_drawable_extension_v2
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_count_v2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (Z : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hZdraw : WilliamsonShmoys.HasPlanarDrawingOn Z) :
    ∃ W : SimpleGraph V, Z ≤ W ∧
      WilliamsonShmoys.HasPlanarDrawingOn W ∧
      W.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨W, hZW, hWdraw, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_drawable_extension_v2 Z hZdraw
  refine ⟨W, hZW, hWdraw, ?_⟩
  exact WilliamsonShmoys.maximal_drawable_edge_count_v2 W hCard hWdraw hmax
