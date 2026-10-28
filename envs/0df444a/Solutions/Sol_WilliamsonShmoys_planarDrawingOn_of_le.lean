-- Prove2me | solution 1 for WilliamsonShmoys.planarDrawingOn_of_le
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T01:29:48.032343+00:00
-- url     : https://prove2.me/submissions/9bcb22aa-4597-4838-93ee-3fa269298e14

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    {G H : SimpleGraph V}
    (hGH : G ≤ H)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    WilliamsonShmoys.HasPlanarDrawingOn G := by
  rcases hH with ⟨p, arc, hp, hEdges, hDisjoint⟩
  refine ⟨p, arc, hp, ?_, ?_⟩
  · intro u v huv hG
    exact hEdges u v huv (hGH hG)
  · intro u v x y huv hxy hG hG' hne t ht s hs heq
    exact hDisjoint u v x y huv hxy (hGH hG) (hGH hG') hne t ht s hs heq