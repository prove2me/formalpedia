-- Prove2me | solution 1 for WilliamsonShmoys.hasPlanarDrawingOn_of_le
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T05:43:33.12244+00:00
-- url     : https://prove2.me/submissions/73a9a355-72ee-4ecf-9df2-33e703780a46

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    {G H : SimpleGraph V} (hGH : G ≤ H)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    WilliamsonShmoys.HasPlanarDrawingOn G := by
  obtain ⟨p, arc, hp, hedge, hcross⟩ := hH
  refine ⟨p, arc, hp, ?_, ?_⟩
  · intro u v huv hGuv
    exact hedge u v huv (hGH hGuv)
  · intro u v x y huv hxy hGuv hGxy hne t ht s hs heq
    exact hcross u v x y huv hxy (hGH hGuv) (hGH hGxy) hne t ht s hs heq