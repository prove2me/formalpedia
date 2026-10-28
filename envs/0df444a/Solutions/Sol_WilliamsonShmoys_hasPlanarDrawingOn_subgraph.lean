-- Prove2me | solution 1 for WilliamsonShmoys.hasPlanarDrawingOn_subgraph
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T06:37:24.818788+00:00
-- url     : https://prove2.me/submissions/0f3fa465-043c-41a4-83a7-77d208f27a62

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    {G H : SimpleGraph V}
    (hGH : Set.Subset G.edgeSet H.edgeSet)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    WilliamsonShmoys.HasPlanarDrawingOn G := by
  have hA : ∀ {u v : V}, G.Adj u v → H.Adj u v := fun {u v} h =>
    (SimpleGraph.mem_edgeSet H).1 (hGH ((SimpleGraph.mem_edgeSet G).2 h))
  obtain ⟨p, arc, hp, h1, h2⟩ := hH
  exact ⟨p, arc, hp, fun u v huv hadj => h1 u v huv (hA hadj),
    fun u v x y huv hxy h3 h4 hne => h2 u v x y huv hxy (hA h3) (hA h4) hne⟩
