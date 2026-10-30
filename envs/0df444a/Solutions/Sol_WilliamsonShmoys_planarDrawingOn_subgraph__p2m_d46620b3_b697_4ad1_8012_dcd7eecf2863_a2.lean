-- Prove2me | solution 1 for WilliamsonShmoys.planarDrawingOn_subgraph__p2m_d46620b3_b697_4ad1_8012_dcd7eecf2863_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:47:15.357506+00:00
-- url     : https://prove2.me/submissions/ab1c08df-8a5f-4df5-8891-9b009701089a

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] {G H : SimpleGraph V}
    (hGH : G ≤ H) (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    WilliamsonShmoys.HasPlanarDrawingOn G := by
  rcases hH with ⟨p, arc, hp, hdraw, hcross⟩
  refine ⟨p, arc, hp, ?_, ?_⟩
  · intro u v huv hadj
    exact hdraw u v huv (hGH hadj)
  · intro u v x y huv hxy hadj hxyadj hne t ht s hs heq
    exact hcross u v x y huv hxy (hGH hadj) (hGH hxyadj) hne t ht s hs heq