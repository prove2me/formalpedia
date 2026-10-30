-- Prove2me | solution 1 for WilliamsonShmoys.planarDrawingOn_subgraph__p2m_fe1a9c4f_5aad_4a32_a050_44f6e8cc3efe_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:25:40.980874+00:00
-- url     : https://prove2.me/submissions/3afcc4d6-d5f9-4ff5-8a1c-acc2b21ff7c5

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] {G H : SimpleGraph V}
    (hGH : G ≤ H) (hH : HasPlanarDrawingOn H) : HasPlanarDrawingOn G := by
  rcases hH with ⟨p, arc, hp, hEdges, hCross⟩
  refine ⟨p, arc, hp, ?_, ?_⟩
  · intro u v huv hG
    exact hEdges u v huv (hGH hG)
  · intro u v x y huv hxy hGuv hGxy hne t ht s hs heq
    exact hCross u v x y huv hxy (hGH hGuv) (hGH hGxy) hne t ht s hs heq