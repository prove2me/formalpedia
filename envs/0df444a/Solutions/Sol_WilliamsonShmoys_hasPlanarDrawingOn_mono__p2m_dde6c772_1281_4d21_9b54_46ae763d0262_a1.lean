-- Prove2me | solution 1 for WilliamsonShmoys.hasPlanarDrawingOn_mono__p2m_dde6c772_1281_4d21_9b54_46ae763d0262_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:57:19.499463+00:00
-- url     : https://prove2.me/submissions/35ce4c8f-24bb-4635-9ba5-f3b9ad612497

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] {G H : SimpleGraph V}
    (hGH : LE.le G H) (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    WilliamsonShmoys.HasPlanarDrawingOn G := by
  rcases hH with ⟨p, arc, hp, h_edges, h_crossings⟩
  refine ⟨p, arc, hp, ?_, ?_⟩
  · intro u v huv hGuv
    exact h_edges u v huv (hGH hGuv)
  · intro u v x y huv hxy hGuv hGxy hne t ht s hs h_eq
    exact h_crossings u v x y huv hxy (hGH hGuv) (hGH hGxy) hne t ht s hs h_eq