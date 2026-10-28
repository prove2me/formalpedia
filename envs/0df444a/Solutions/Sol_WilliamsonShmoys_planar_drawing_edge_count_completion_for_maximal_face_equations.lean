-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_count_completion_for_maximal_face_equations
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T04:02:09.561197+00:00
-- url     : https://prove2.me/submissions/093c8222-9386-4901-bf65-e1b4511a259d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_completion_for_maximal_face_equations_drawable_maximal_extension
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_completion_for_maximal_face_equations_maximal_edge_count

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      N ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hNK, hK, hMax⟩ :=
    WilliamsonShmoys.planar_drawing_edge_count_completion_for_maximal_face_equations_drawable_maximal_extension
      N hN
  refine ⟨K, hNK, hK, ?_⟩
  exact WilliamsonShmoys.planar_drawing_edge_count_completion_for_maximal_face_equations_maximal_edge_count
    K hK hCard hMax