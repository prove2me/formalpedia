-- Prove2me | solution 1 for WilliamsonShmoys.hasPlanarDrawingOn_mono__p2m_2dea5b09_c429_4a5e_b3c1_b82fac24916e_a2
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-04T18:39:14.304393+00:00
-- url     : https://prove2.me/submissions/4f761f61-aeeb-4610-9807-10d49f953506

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    {G H : SimpleGraph V} (hHG : H ≤ G) :
    WilliamsonShmoys.HasPlanarDrawingOn G →
      WilliamsonShmoys.HasPlanarDrawingOn H := by
  rintro ⟨p, arc, hp, hsingle, hpair⟩
  refine ⟨p, arc, hp, ?_, ?_⟩
  · intro u v huv hHuv
    exact hsingle u v huv (hHG hHuv)
  · intro u v x y huv hxy hHuv hHxy hne t ht s hs heq
    exact hpair u v x y huv hxy (hHG hHuv) (hHG hHxy) hne t ht s hs heq
