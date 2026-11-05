-- Prove2me | solution 1 for WilliamsonShmoys.hasPlanarDrawingOn_mono__p2m_3647f07c_750e_4c3e_8be8_ca29b1e4d823_a1
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-04T17:36:18.561447+00:00
-- url     : https://prove2.me/submissions/32838b82-7f43-4e1e-8f9b-5c2f50151824

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] {G J : SimpleGraph V}
    (hGJ : G ≤ J) (hJ : HasPlanarDrawingOn J) : HasPlanarDrawingOn G := by
  rcases hJ with ⟨p, arc, hp, hsingle, hpair⟩
  refine ⟨p, arc, hp, ?_, ?_⟩
  · intro u v huv hGuv
    exact hsingle u v huv (hGJ hGuv)
  · intro u v x y huv hxy hGuv hGxy hne t ht s hs heq
    exact hpair u v x y huv hxy (hGJ hGuv) (hGJ hGxy) hne t ht s hs heq
