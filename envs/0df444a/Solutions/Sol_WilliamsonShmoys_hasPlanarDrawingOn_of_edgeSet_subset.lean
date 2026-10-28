-- Prove2me | solution 1 for WilliamsonShmoys.hasPlanarDrawingOn_of_edgeSet_subset
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T06:25:37.848666+00:00
-- url     : https://prove2.me/submissions/c5286171-1ca8-42cc-9adf-7deaac0f87e9

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    {G H : SimpleGraph V}
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hGH : G.edgeSet ⊆ H.edgeSet) :
    WilliamsonShmoys.HasPlanarDrawingOn G := by
  rcases hH with ⟨p, arc, hp, hEdges, hCrossings⟩
  refine ⟨p, arc, hp, ?_, ?_⟩
  · intro u v huvlt huv
    apply hEdges u v huvlt
    exact (SimpleGraph.mem_edgeSet H).mp
      (hGH ((SimpleGraph.mem_edgeSet G).mpr huv))
  · intro u v x y huvlt hxylt huv hxy hne t ht s hs hEq
    exact hCrossings u v x y huvlt hxylt
      ((SimpleGraph.mem_edgeSet H).mp
        (hGH ((SimpleGraph.mem_edgeSet G).mpr huv)))
      ((SimpleGraph.mem_edgeSet H).mp
        (hGH ((SimpleGraph.mem_edgeSet G).mpr hxy)))
      hne t ht s hs hEq