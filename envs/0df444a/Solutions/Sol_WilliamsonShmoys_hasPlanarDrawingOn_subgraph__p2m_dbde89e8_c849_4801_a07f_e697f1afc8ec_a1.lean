-- Prove2me | solution 1 for WilliamsonShmoys.hasPlanarDrawingOn_subgraph__p2m_dbde89e8_c849_4801_a07f_e697f1afc8ec_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T03:14:26.002185+00:00
-- url     : https://prove2.me/submissions/a87aba0a-6223-4c51-8a65-51c4fa5420b1

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    {G G' : SimpleGraph V} (h : G ≤ G')
    (hG' : WilliamsonShmoys.HasPlanarDrawingOn G') :
    WilliamsonShmoys.HasPlanarDrawingOn G := by
  rcases hG' with ⟨p, arc, hp, hEdges, hCrossings⟩
  refine ⟨p, arc, hp, ?_, ?_⟩
  · intro u v huv hAdj
    exact hEdges u v huv (h hAdj)
  · intro u v x y huv hxy hAdj hAdj' hPair t ht s hs hEq
    exact hCrossings u v x y huv hxy (h hAdj) (h hAdj') hPair t ht s hs hEq