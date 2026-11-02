-- Prove2me | solution 1 for WilliamsonShmoys.planarDrawingOn_subgraph__p2m_3bb112e2_2df9_4e3a_a157_84b2375941f4_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T08:09:20.441556+00:00
-- url     : https://prove2.me/submissions/65fff427-be6a-4633-b300-794810d24863

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    {G H : SimpleGraph V} (hHG : H ≤ G)
    (hG : HasPlanarDrawingOn G) : HasPlanarDrawingOn H := by
  rcases hG with ⟨p, arc, hp, hedge, hcross⟩
  refine ⟨p, arc, hp, ?_, ?_⟩
  · intro u v huv hadj
    exact hedge u v huv (hHG hadj)
  · intro u v x y huv hxy hadjuv hadjxy hne t ht s hs heq
    exact hcross u v x y huv hxy (hHG hadjuv) (hHG hadjxy) hne t ht s hs heq