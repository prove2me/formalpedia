-- Prove2me | solution 1 for WilliamsonShmoys.hasPlanarDrawingOn_mono__p2m_168460db_bad2_471e_a83e_74dae3ce8af4_a1
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-04T17:34:42.602956+00:00
-- url     : https://prove2.me/submissions/e96555eb-0c8a-4a66-930b-f0d89f9bde49

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    {G H : SimpleGraph V}
    (hGH : G ≤ H) :
    HasPlanarDrawingOn H → HasPlanarDrawingOn G := by
  rintro ⟨p, arc, hp, hsingle, hpair⟩
  refine ⟨p, arc, hp, ?_, ?_⟩
  · intro u v huv hGuv
    exact hsingle u v huv (hGH hGuv)
  · intro u v x y huv hxy hGuv hGxy hne t ht s hs heq
    exact hpair u v x y huv hxy (hGH hGuv) (hGH hGxy) hne t ht s hs heq
