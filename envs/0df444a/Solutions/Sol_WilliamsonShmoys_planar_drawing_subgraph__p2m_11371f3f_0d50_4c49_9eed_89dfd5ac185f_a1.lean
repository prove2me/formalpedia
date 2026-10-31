-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_subgraph__p2m_11371f3f_0d50_4c49_9eed_89dfd5ac185f_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:23:50.417584+00:00
-- url     : https://prove2.me/submissions/7d876a19-cd7a-452b-8550-56e714c987f1

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] {G H : SimpleGraph V}
    (hGH : ∀ ⦃u v : V⦄, G.Adj u v → H.Adj u v)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    WilliamsonShmoys.HasPlanarDrawingOn G := by
  rcases hH with ⟨p, arc, hp, hEdge, hCross⟩
  refine ⟨p, arc, hp, ?_, ?_⟩
  · intro u v huv hGuv
    exact hEdge u v huv (hGH hGuv)
  · intro u v x y huv hxy hGuv hGxy hne t ht s hs hEq
    exact hCross u v x y huv hxy (hGH hGuv) (hGH hGxy) hne t ht s hs hEq