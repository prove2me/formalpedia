-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_disconnected_strict_step__p2m_8e1589da_8236_4d2f_a43b_c94137df9ddf_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:04:59.109708+00:00
-- url     : https://prove2.me/submissions/3a50445a-ecd3-4ce9-a822-f55a066df60e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_disconnected_has_nonreachable_pair__p2m_8cea35d0_1902_4066_a769_e5349d5dbcd7_a1
import Theorems.Thm_WilliamsonShmoys_planar_drawing_insert_nonreachable_pair__p2m_8cea35d0_1902_4066_a769_e5349d5dbcd7_a1
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hH : HasPlanarDrawingOn H) (hDisconnected : ¬ H.Connected) :
    ∃ H' : SimpleGraph V, H < H' ∧ HasPlanarDrawingOn H' := by
  obtain ⟨u, v, huv⟩ :=
    WilliamsonShmoys.disconnected_has_nonreachable_pair__p2m_8cea35d0_1902_4066_a769_e5349d5dbcd7_a1
      H hDisconnected
  exact
    WilliamsonShmoys.planar_drawing_insert_nonreachable_pair__p2m_8cea35d0_1902_4066_a769_e5349d5dbcd7_a1
      H hH u v huv