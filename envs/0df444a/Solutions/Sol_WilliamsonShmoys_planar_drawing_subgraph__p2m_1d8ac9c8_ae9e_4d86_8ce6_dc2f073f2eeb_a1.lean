-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_subgraph__p2m_1d8ac9c8_ae9e_4d86_8ce6_dc2f073f2eeb_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:30:23.962993+00:00
-- url     : https://prove2.me/submissions/1a52fd59-ff08-402d-bdb7-dfc3983112f8

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    {G H : SimpleGraph V} (hGH : G ≤ H)
    (hH : HasPlanarDrawingOn H) :
    HasPlanarDrawingOn G := by
  rcases hH with ⟨p, arc, hp, hedges, hcross⟩
  refine ⟨p, arc, hp, ?_, ?_⟩
  · intro u v huv hGuv
    exact hedges u v huv (hGH hGuv)
  · intro u v x y huv hxy hGuv hGxy hne t ht s hs heq
    exact hcross u v x y huv hxy (hGH hGuv) (hGH hGxy)
      hne t ht s hs heq