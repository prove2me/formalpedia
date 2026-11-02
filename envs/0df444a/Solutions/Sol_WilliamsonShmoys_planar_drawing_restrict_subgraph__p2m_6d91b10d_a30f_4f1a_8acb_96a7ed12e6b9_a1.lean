-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_restrict_subgraph__p2m_6d91b10d_a30f_4f1a_8acb_96a7ed12e6b9_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:57:59.350543+00:00
-- url     : https://prove2.me/submissions/7d849968-665c-42c3-b240-a7e0ec14f158

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M N : SimpleGraph V) (hMN : M ≤ N)
    (hNdraw : WilliamsonShmoys.HasPlanarDrawingOn N) :
    WilliamsonShmoys.HasPlanarDrawingOn M := by
  rcases hNdraw with ⟨p, arc, hp, hedge, hcross⟩
  refine ⟨p, arc, hp, ?_, ?_⟩
  · intro u v huv hMuv
    exact hedge u v huv (hMN hMuv)
  · intro u v x y huv hxy hMuv hMxy hne t ht s hs heq
    exact hcross u v x y huv hxy (hMN hMuv) (hMN hMxy) hne t ht s hs heq