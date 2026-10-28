-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawingOn_subgraph
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T11:35:12.036991+00:00
-- url     : https://prove2.me/submissions/aa28e2d7-837e-4c08-b916-93188f618e29

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    {G H : SimpleGraph V} (hGH : G ≤ H)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    WilliamsonShmoys.HasPlanarDrawingOn G := by
  rcases hH with ⟨p, arc, hp, hedge, hcross⟩
  refine ⟨p, arc, hp, ?_, ?_⟩
  · intro u v huv hGuv
    exact hedge u v huv (hGH hGuv)
  · intro u v x y huv hxy hGuv hGxy hne t ht s hs heq
    exact hcross u v x y huv hxy (hGH hGuv) (hGH hGxy) hne t ht s hs heq