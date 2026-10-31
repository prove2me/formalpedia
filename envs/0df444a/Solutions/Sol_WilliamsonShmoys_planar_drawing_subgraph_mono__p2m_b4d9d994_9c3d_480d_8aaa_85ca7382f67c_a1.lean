-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_subgraph_mono__p2m_b4d9d994_9c3d_480d_8aaa_85ca7382f67c_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:00:18.699257+00:00
-- url     : https://prove2.me/submissions/744cedc7-8a56-4159-af56-2f92bd56a2da

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (B A : SimpleGraph V)
    (hBA : B ≤ A) (hA : HasPlanarDrawingOn A) : HasPlanarDrawingOn B := by
  rcases hA with ⟨p, arc, hp, hEdges, hCrossings⟩
  refine ⟨p, arc, hp, ?_, ?_⟩
  · intro u v huv hB
    exact hEdges u v huv (hBA hB)
  · intro u v x y huv hxy hB hB' hne t ht s hs heq
    exact hCrossings u v x y huv hxy (hBA hB) (hBA hB') hne t ht s hs heq