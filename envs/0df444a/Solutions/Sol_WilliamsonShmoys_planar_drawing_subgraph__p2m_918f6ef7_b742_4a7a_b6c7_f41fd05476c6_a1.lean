-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_subgraph__p2m_918f6ef7_b742_4a7a_b6c7_f41fd05476c6_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:42:57.392252+00:00
-- url     : https://prove2.me/submissions/4414bbaa-1ea7-402a-9588-b8d6db45f55d

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    {G H : SimpleGraph V} (hHG : H ≤ G) (hG : HasPlanarDrawingOn G) :
    HasPlanarDrawingOn H := by
  rcases hG with ⟨p, arc, hp, hedge, hcross⟩
  refine ⟨p, arc, hp, ?_, ?_⟩
  · intro u v huv hH
    exact hedge u v huv (hHG hH)
  · intro u v x y huv hxy huvH hxyH hne t ht s hs hEq
    exact hcross u v x y huv hxy (hHG huvH) (hHG hxyH) hne t ht s hs hEq