-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_edge_count_for_triangulation_extension
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T21:16:06.26333+00:00
-- url     : https://prove2.me/submissions/ea2a7a75-aa50-4260-b672-f7a46602c6c0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawable_graph_has_triangulated_extension_edge_count

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (Z : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hZdraw : WilliamsonShmoys.HasPlanarDrawingOn Z)
    (hmax : ∀ W : SimpleGraph V, Z ≤ W →
      WilliamsonShmoys.HasPlanarDrawingOn W → W ≤ Z) :
    Z.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨W, hZW, hWdraw, hCount⟩ :=
    WilliamsonShmoys.drawable_graph_has_triangulated_extension_edge_count Z hCard hZdraw
  have hWZ : W ≤ Z := hmax W hZW hWdraw
  have hEdges : Z.edgeSet = W.edgeSet := by
    apply Set.Subset.antisymm
    · exact SimpleGraph.edgeSet_mono hZW
    · exact SimpleGraph.edgeSet_mono hWZ
  simpa only [hEdges] using hCount
