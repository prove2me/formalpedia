-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_augmentation__p2m_01732aef_dd3e_4b78_a11c_771f0411d541_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:17:53.075203+00:00
-- url     : https://prove2.me/submissions/e666325f-282f-44da-b3cc-fe4d6e59a033
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_drawing_bridge_step__p2m_5de40fa3_9823_4b85_b185_5f75a9f0282e_a2
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_from_bridge_steps__p2m_5de40fa3_9823_4b85_b185_5f75a9f0282e_a2

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : HasPlanarDrawingOn K)
    (hcard : LE.le 3 (Fintype.card V)) :
    Exists fun H : SimpleGraph V => And (LE.le K H)
      (And (HasPlanarDrawingOn H) H.Connected) := by
  exact WilliamsonShmoys.planar_drawing_connected_from_bridge_steps__p2m_5de40fa3_9823_4b85_b185_5f75a9f0282e_a2
    K hK hcard
    (fun G hG A hA hAc hno =>
      WilliamsonShmoys.planar_drawing_bridge_step__p2m_5de40fa3_9823_4b85_b185_5f75a9f0282e_a2
        G hG A hA hAc hno)