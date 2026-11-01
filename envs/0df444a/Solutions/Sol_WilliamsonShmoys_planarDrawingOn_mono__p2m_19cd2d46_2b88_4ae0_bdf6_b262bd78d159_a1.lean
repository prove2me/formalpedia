-- Prove2me | solution 1 for WilliamsonShmoys.planarDrawingOn_mono__p2m_19cd2d46_2b88_4ae0_bdf6_b262bd78d159_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T03:11:57.654871+00:00
-- url     : https://prove2.me/submissions/7519312c-f866-447f-8292-dad4845c49a1

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G H : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hsub : ∀ a b, H.Adj a b → G.Adj a b) :
    WilliamsonShmoys.HasPlanarDrawingOn H := by
  rcases hG with ⟨p, arc, hp, hEdges, hCrossings⟩
  refine ⟨p, arc, hp, ?_, ?_⟩
  · intro u v huv hAdj
    exact hEdges u v huv (hsub u v hAdj)
  · intro u v x y huv hxy huvAdj hxyAdj hne t ht s hs heq
    exact hCrossings u v x y huv hxy
      (hsub u v huvAdj) (hsub x y hxyAdj) hne t ht s hs heq