-- Prove2me | solution 1 for WilliamsonShmoys.planarDrawingOn_mono__p2m_6822b8c0_b310_4ef6_afea_d822182653e7_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:21:57.044507+00:00
-- url     : https://prove2.me/submissions/f7c47a19-de54-4183-bbb4-f2590c515b8d

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    {G F : SimpleGraph V} (hGF : G ≤ F)
    (hF : WilliamsonShmoys.HasPlanarDrawingOn F) :
    WilliamsonShmoys.HasPlanarDrawingOn G := by
  rcases hF with ⟨p, arc, hp, hArc, hNoCross⟩
  refine ⟨p, arc, hp, ?_, ?_⟩
  · intro u v huv hG
    exact hArc u v huv (hGF hG)
  · intro u v x y huv hxy hGuv hGxy hne t ht s hs heq
    exact hNoCross u v x y huv hxy (hGF hGuv) (hGF hGxy) hne t ht s hs heq