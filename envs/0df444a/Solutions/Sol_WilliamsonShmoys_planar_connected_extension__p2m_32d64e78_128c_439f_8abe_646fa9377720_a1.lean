-- Prove2me | solution 1 for WilliamsonShmoys.planar_connected_extension__p2m_32d64e78_128c_439f_8abe_646fa9377720_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T22:10:50.036993+00:00
-- url     : https://prove2.me/submissions/6e6be4de-8133-4ffb-9122-e007a380da34
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_connected_extension_of_strict_extension__p2m_5b4ba625_e76a_490b_a06e_75a37c9ee7a0_a1
import Theorems.Thm_WilliamsonShmoys_planar_strict_extension_of_disconnected_drawing__p2m_5b4ba625_e76a_490b_a06e_75a37c9ee7a0_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H)
    (hV : 3 <= Fintype.card V) :
    Exists fun K : SimpleGraph V => And (LE.le H K) (And K.Connected (HasPlanarDrawingOn K)) := by
  exact WilliamsonShmoys.planar_connected_extension_of_strict_extension__p2m_5b4ba625_e76a_490b_a06e_75a37c9ee7a0_a1 H hH hV (fun G hG hdisc => WilliamsonShmoys.planar_strict_extension_of_disconnected_drawing__p2m_5b4ba625_e76a_490b_a06e_75a37c9ee7a0_a1 G hG hV hdisc)