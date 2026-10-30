-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_subgraph_hereditary__p2m_870bfd2f_4ca1_482a_946e_00772601b2f5_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:44:27.786027+00:00
-- url     : https://prove2.me/submissions/8c8c9135-490d-46fa-b423-189323e5ea3e

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    {G H : SimpleGraph V}
    (hHG : H ≤ G)
    (hDraw : HasPlanarDrawingOn G) :
    HasPlanarDrawingOn H := by
  rcases hDraw with ⟨p, arc, hp, hEdge, hCross⟩
  refine ⟨p, arc, hp, ?_, ?_⟩
  · intro u v huv hH
    exact hEdge u v huv (hHG hH)
  · intro u v x y huv hxy hHuv hHxy hne t ht s hs hEq
    exact hCross u v x y huv hxy (hHG hHuv) (hHG hHxy) hne t ht s hs hEq