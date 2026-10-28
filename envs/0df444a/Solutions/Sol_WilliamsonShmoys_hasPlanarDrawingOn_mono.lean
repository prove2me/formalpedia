-- Prove2me | solution 1 for WilliamsonShmoys.hasPlanarDrawingOn_mono
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-25T23:29:43.442232+00:00
-- url     : https://prove2.me/submissions/d4488d83-bbc2-468e-8e52-ea44fbd2cc66

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    {G H : SimpleGraph V} (hGH : G ≤ H)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    WilliamsonShmoys.HasPlanarDrawingOn G := by
  rcases hH with ⟨p, arc, hp_inj, hedge, hcross⟩
  refine ⟨p, arc, hp_inj, ?_, ?_⟩
  · intro u v huv hGuv
    exact hedge u v huv (hGH hGuv)
  · intro u v x y huv hxy hGuv hGxy hne t ht s hs heq
    exact hcross u v x y huv hxy (hGH hGuv) (hGH hGxy) hne t ht s hs heq