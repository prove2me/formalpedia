-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_subgraph__p2m_a41ba058_0926_4932_8131_302826679a62_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:09:37.526198+00:00
-- url     : https://prove2.me/submissions/416dd78a-8de7-4629-ad07-1fa57d4af563

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

 theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G H : SimpleGraph V)
    (hGH : G ≤ H)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    WilliamsonShmoys.HasPlanarDrawingOn G := by
  rcases hH with ⟨p, arc, hp, hcurve, hdisjoint⟩
  refine ⟨p, arc, hp, ?_, ?_⟩
  · intro u v huv hGuv
    exact hcurve u v huv (hGH hGuv)
  · intro u v x y huv hxy hGuv hGxy hne t ht s hs hEq
    exact hdisjoint u v x y huv hxy (hGH hGuv) (hGH hGxy) hne t ht s hs hEq