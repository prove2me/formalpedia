-- Prove2me | solution 1 for WilliamsonShmoys_hasPlanarDrawingOn_mono__p2m_f3863ecb_d96f_4f01_8e13_caf8f4700d63_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T03:12:21.884239+00:00
-- url     : https://prove2.me/submissions/fc91e75e-4025-4646-b16f-87aa5444d521

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    {G H : SimpleGraph V} (hGH : G ≤ H)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    WilliamsonShmoys.HasPlanarDrawingOn G := by
  rcases hH with ⟨p, arc, hp, hEdges, hCross⟩
  refine ⟨p, arc, hp, ?_, ?_⟩
  · intro u v huv hadj
    exact hEdges u v huv (hGH hadj)
  · intro u v x y huv hxy hadjU hadjX hne t ht s hs hEq
    exact hCross u v x y huv hxy (hGH hadjU) (hGH hadjX) hne t ht s hs hEq