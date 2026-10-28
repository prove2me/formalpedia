-- Prove2me | solution 1 for WilliamsonShmoys.planar_augmentation_euler_count_16de6deb_de5f_4a25_8b3a_216fac552bd1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T12:59:01.917277+00:00
-- url     : https://prove2.me/submissions/540ad6c8-c970-46f3-be7f-f3f0958a9a82
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension_for_euler_count
import Theorems.Thm_WilliamsonShmoys_maximal_planar_euler_count_for_augmentation

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ M : SimpleGraph V, L ≤ M ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      M.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨M, hLM, hM, hMax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_extension_for_euler_count L hL
  exact ⟨M, hLM, hM,
    WilliamsonShmoys.maximal_planar_euler_count_for_augmentation M hM hCard hMax⟩