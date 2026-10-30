-- Prove2me | solution 1 for WilliamsonShmoys.drawable_subgraph__p2m_39578764_0198_4707_9e11_eef0219b5111_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:34:54.818671+00:00
-- url     : https://prove2.me/submissions/b1a9ec21-3507-4be0-a5c2-d2b305d6cf5c

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    {G H : SimpleGraph V} (hGH : G ≤ H)
    (hDraw : HasPlanarDrawingOn H) : HasPlanarDrawingOn G := by
  rcases hDraw with ⟨p, arc, hp, hEdges, hCrossings⟩
  refine ⟨p, arc, hp, ?_, ?_⟩
  · intro u v huv hG
    exact hEdges u v huv (hGH hG)
  · intro u v x y huv hxy hG hG' hne t ht s hs heq
    exact hCrossings u v x y huv hxy (hGH hG) (hGH hG') hne t ht s hs heq