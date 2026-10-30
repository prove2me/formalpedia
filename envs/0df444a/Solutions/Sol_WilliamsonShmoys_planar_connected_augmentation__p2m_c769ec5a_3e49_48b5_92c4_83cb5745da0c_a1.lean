-- Prove2me | solution 1 for WilliamsonShmoys.planar_connected_augmentation__p2m_c769ec5a_3e49_48b5_92c4_83cb5745da0c_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T22:30:04.93898+00:00
-- url     : https://prove2.me/submissions/7c5b01c5-c2f8-431c-933f-1db6e1f5e513
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_augmentation_of_edge_step__p2m_3d18ba84_dae9_4abe_9f72_3fa917a9726c_a1
import Theorems.Thm_WilliamsonShmoys_planar_one_edge_insertion_of_card_ge_three__p2m_3d18ba84_dae9_4abe_9f72_3fa917a9726c_a3

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H)
    (hV : 3 <= Fintype.card V) :
    Exists fun K : SimpleGraph V =>
      And (H.edgeSet.ncard <= K.edgeSet.ncard)
        (And (HasPlanarDrawingOn K) K.Connected) := by
  exact WilliamsonShmoys.planar_augmentation_of_edge_step__p2m_3d18ba84_dae9_4abe_9f72_3fa917a9726c_a1
    hV
    (fun G hG hG_not_connected =>
      WilliamsonShmoys.planar_one_edge_insertion_of_card_ge_three__p2m_3d18ba84_dae9_4abe_9f72_3fa917a9726c_a3
        hV G hG hG_not_connected)
    H hH