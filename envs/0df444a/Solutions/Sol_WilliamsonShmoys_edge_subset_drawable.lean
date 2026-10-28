-- Prove2me | solution 1 for WilliamsonShmoys.edge_subset_drawable
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T21:06:52.873265+00:00
-- url     : https://prove2.me/submissions/2ac9ce8b-f52b-4d1a-8a0b-58cd5b969125

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    {G H : SimpleGraph V}
    (hGH : G.edgeSet ⊆ H.edgeSet)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H) :
    WilliamsonShmoys.HasPlanarDrawingOn G := by
  rcases hDraw with ⟨p, arc, hp, hedges, hcross⟩
  have hle : G ≤ H := SimpleGraph.edgeSet_subset_edgeSet.mp hGH
  refine ⟨p, arc, hp, ?_, ?_⟩
  · intro u v huv hG
    exact hedges u v huv ((SimpleGraph.le_iff_adj.mp hle) u v hG)
  · intro u v x y huv hxy hGu hGx hpair
    exact hcross u v x y huv hxy
      ((SimpleGraph.le_iff_adj.mp hle) u v hGu)
      ((SimpleGraph.le_iff_adj.mp hle) x y hGx) hpair