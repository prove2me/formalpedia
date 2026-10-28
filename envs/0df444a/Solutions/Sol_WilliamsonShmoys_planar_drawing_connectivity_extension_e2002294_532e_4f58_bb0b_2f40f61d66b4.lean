-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connectivity_extension_e2002294_532e_4f58_bb0b_2f40f61d66b4
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T17:44:20.523545+00:00
-- url     : https://prove2.me/submissions/8c53a5e1-9317-4935-8e6a-9beabca16b48
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_insertion_step
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_extension_of_edge_insertions

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hdraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K' : SimpleGraph V, K ≤ K' ∧ K'.Connected ∧
      WilliamsonShmoys.HasPlanarDrawingOn K' ∧
      K.edgeSet.ncard ≤ K'.edgeSet.ncard := by
  exact WilliamsonShmoys.planar_drawing_connected_extension_of_edge_insertions
    K hdraw hV (by
      intro L hKL hLdraw hLnc
      exact WilliamsonShmoys.planar_drawing_edge_insertion_step L hLdraw hLnc)