-- Prove2me | solution 1 for WilliamsonShmoys.planarDrawingOn_of_le__p2m_138d462c_20bd_43cc_9c59_565c454fd505_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T15:44:19.153734+00:00
-- url     : https://prove2.me/submissions/e0c4a810-affa-4f4a-845f-eb87f55db703

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    {H K : SimpleGraph V} (hHK : H ≤ K)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    WilliamsonShmoys.HasPlanarDrawingOn H := by
  rcases hK with ⟨p, arc, hp, hEdges, hCrossings⟩
  refine ⟨p, arc, hp, ?_, ?_⟩
  · intro u v huv hHuv
    exact hEdges u v huv (hHK hHuv)
  · intro u v x y huv hxy hHuv hHxy hne t ht s hs heq
    exact hCrossings u v x y huv hxy (hHK hHuv) (hHK hHxy) hne t ht s hs heq