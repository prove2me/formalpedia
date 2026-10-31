-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_subgraph__p2m_8fae69ca_ae24_46cb_a1af_2dc3b1fd2851_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:14:05.600919+00:00
-- url     : https://prove2.me/submissions/2c790e41-29ea-40df-a41e-88e4dcf3aca8

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    {A B : SimpleGraph V} (hAB : A ≤ B)
    (hB : HasPlanarDrawingOn B) : HasPlanarDrawingOn A := by
  rcases hB with ⟨p, arc, hp, hedge, hcross⟩
  refine ⟨p, arc, hp, ?_, ?_⟩
  · intro u v huv hA
    exact hedge u v huv (hAB hA)
  · intro u v x y huv hxy hA hAx hne t ht s hs heq
    exact hcross u v x y huv hxy (hAB hA) (hAB hAx) hne t ht s hs heq