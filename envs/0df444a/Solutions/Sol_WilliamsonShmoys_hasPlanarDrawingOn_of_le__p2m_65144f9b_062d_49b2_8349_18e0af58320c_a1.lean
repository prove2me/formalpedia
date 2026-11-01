-- Prove2me | solution 1 for WilliamsonShmoys.hasPlanarDrawingOn_of_le__p2m_65144f9b_062d_49b2_8349_18e0af58320c_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:35:01.330541+00:00
-- url     : https://prove2.me/submissions/d43fd47a-08f7-464a-af3b-595a817f2cda

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    {G H : SimpleGraph V}
    (hGH : G ≤ H)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    WilliamsonShmoys.HasPlanarDrawingOn G := by
  rcases hH with ⟨p, arc, hp, hedge, hdisjoint⟩
  refine ⟨p, arc, hp, ?_, ?_⟩
  · intro u v huv hAdj
    exact hedge u v huv (hGH hAdj)
  · intro u v x y huv hxy huvAdj hxyAdj hne t ht s hs heq
    exact hdisjoint u v x y huv hxy (hGH huvAdj) (hGH hxyAdj) hne t ht s hs heq