-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_upper_bound_for_counting
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T01:40:20.663267+00:00
-- url     : https://prove2.me/submissions/b9b73f8c-83fa-47d1-b47b-ac5401a5c2a2

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_augmented_euler_data_1f26b2b1_f51b_4e13_bfd7_806af5753a70
import Mathlib

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    (K.edgeSet.ncard : Int) <= 3 * (Fintype.card V : Int) - 6 := by
  obtain ⟨M, f, hm, heuler, hfaces⟩ :=
    WilliamsonShmoys.planar_drawing_augmented_euler_data_1f26b2b1_f51b_4e13_bfd7_806af5753a70 K hV hK
  omega