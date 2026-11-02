-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_on_subgraph__p2m_5269810a_aaa3_482e_ac1c_32cbc68ffb91_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T16:51:44.347403+00:00
-- url     : https://prove2.me/submissions/9310249c-d961-4531-88fe-26cdf832c21f

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    {G H : SimpleGraph V} (hHG : H ≤ G)
    (hG : HasPlanarDrawingOn G) :
    HasPlanarDrawingOn H := by
  rcases hG with ⟨p, arc, hp, hedge, hcross⟩
  refine ⟨p, arc, hp, ?_, ?_⟩
  · intro u v huv hadj
    exact hedge u v huv (hHG hadj)
  · intro u v x y huv hxy hadjuv hadjxy hne t ht s hs heq
    exact hcross u v x y huv hxy (hHG hadjuv) (hHG hadjxy) hne t ht s hs heq