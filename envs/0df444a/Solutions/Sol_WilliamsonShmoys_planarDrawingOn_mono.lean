-- Prove2me | solution 1 for WilliamsonShmoys.planarDrawingOn_mono
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T03:18:41.469299+00:00
-- url     : https://prove2.me/submissions/18c9abe2-ad70-443a-8863-5ae472fa14bd

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    {G H : SimpleGraph V} (hGH : G ≤ H) :
    WilliamsonShmoys.HasPlanarDrawingOn H →
      WilliamsonShmoys.HasPlanarDrawingOn G := by
  intro hH
  unfold WilliamsonShmoys.HasPlanarDrawingOn at hH ⊢
  rcases hH with ⟨p, arc, hp, hedge, hcross⟩
  refine ⟨p, arc, hp, ?_, ?_⟩
  · intro u v huv hG
    exact hedge u v huv (hGH hG)
  · intro u v x y huv hxy hG hG' hne t ht s hs hEq
    exact hcross u v x y huv hxy (hGH hG) (hGH hG') hne t ht s hs hEq