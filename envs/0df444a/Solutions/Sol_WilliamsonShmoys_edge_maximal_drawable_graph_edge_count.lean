-- Prove2me | solution 1 for WilliamsonShmoys.edge_maximal_drawable_graph_edge_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T07:05:33.400118+00:00
-- url     : https://prove2.me/submissions/e7265ba9-8f8e-4139-958f-70e2b32cfc91
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawingOn_triangulation_extension_v2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn U)
    (hV : 3 <= Fintype.card V)
    (hmax : ∀ W : SimpleGraph V,
      (∀ {u v}, U.Adj u v → W.Adj u v) →
      WilliamsonShmoys.HasPlanarDrawingOn W → W = U) :
    U.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨W, hsub, hdrawW, hcount⟩ :=
    WilliamsonShmoys.planar_drawingOn_triangulation_extension_v2 U hdraw hV
  have hWU : W = U := hmax W hsub hdrawW
  simpa [hWU] using hcount