-- Prove2me | solution 1 for WilliamsonShmoys.planarDrawingOn_subgraph__p2m_8c20c3de_e0e6_4d41_88fb_de4af60b0786_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:49:02.847284+00:00
-- url     : https://prove2.me/submissions/f7ff7d17-5617-4bcd-ba07-a626a0bcf67a

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    {G K : SimpleGraph V} (hGK : G ≤ K) (hK : HasPlanarDrawingOn K) :
    HasPlanarDrawingOn G := by
  rcases hK with ⟨p, arc, hp, hEdges, hDisjoint⟩
  refine ⟨p, arc, hp, ?_, ?_⟩
  · intro u v huv hAdj
    exact hEdges u v huv (hGK hAdj)
  · intro u v x y huv hxy hAdjUV hAdjXY hne t ht s hs heq
    exact hDisjoint u v x y huv hxy (hGK hAdjUV) (hGK hAdjXY) hne t ht s hs heq