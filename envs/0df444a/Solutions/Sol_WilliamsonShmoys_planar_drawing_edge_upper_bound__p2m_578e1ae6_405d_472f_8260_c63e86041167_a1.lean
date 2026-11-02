-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_upper_bound__p2m_578e1ae6_405d_472f_8260_c63e86041167_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:57:16.350088+00:00
-- url     : https://prove2.me/submissions/6289620e-387e-4e8f-86bc-a2af2014a038
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_completion__p2m_e26f4eeb_ea90_4bc7_9f3f_02f85b28272b_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hK : HasPlanarDrawingOn K)
    (hV : 3 <= Fintype.card V) :
    K.edgeFinset.card <= 3 * Fintype.card V - 6 := by
  classical
  obtain ⟨H, dH, _hH, _hsub, hle, hcard⟩ :=
    WilliamsonShmoys.planar_drawing_triangulation_completion__p2m_e26f4eeb_ea90_4bc7_9f3f_02f85b28272b_a1
      K hK hV
  letI : DecidableRel H.Adj := dH
  calc
    K.edgeFinset.card <= H.edgeFinset.card := hle
    _ = 3 * Fintype.card V - 6 := hcard