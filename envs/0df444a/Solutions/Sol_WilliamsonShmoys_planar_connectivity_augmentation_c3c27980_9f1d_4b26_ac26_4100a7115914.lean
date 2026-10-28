-- Prove2me | solution 1 for WilliamsonShmoys.planar_connectivity_augmentation_c3c27980_9f1d_4b26_ac26_4100a7115914
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T05:03:39.97403+00:00
-- url     : https://prove2.me/submissions/7f379a87-7bea-4b25-9e30-3b27d2c0ddda
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_graph_completion_of_strict_extension
import Theorems.Thm_WilliamsonShmoys_planar_drawing_strict_supergraph_step

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V)
    (hR : WilliamsonShmoys.HasPlanarDrawingOn R) :
    ∃ S : SimpleGraph V,
      R.edgeSet.ncard ≤ S.edgeSet.ncard ∧
      S.Connected ∧
      WilliamsonShmoys.HasPlanarDrawingOn S := by
  exact WilliamsonShmoys.finite_graph_completion_of_strict_extension
    (P := WilliamsonShmoys.HasPlanarDrawingOn)
    (fun G hG hDisconnected =>
      WilliamsonShmoys.planar_drawing_strict_supergraph_step G hG hDisconnected)
    R hR