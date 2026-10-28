-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulation_completion_retry3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T10:18:06.819985+00:00
-- url     : https://prove2.me/submissions/3c304ed5-5ac0-4fe6-9db8-a86e0ae2c7de
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_completion_retry3_exists_maximal_drawable_supergraph
import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_completion_retry3_maximal_planar_face_decomposition
import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_completion_retry3_edge_count_from_face_equations

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hDraw : HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V, K ≤ L ∧ HasPlanarDrawingOn L ∧
      L.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨L, hKL, hLDraw, hMax⟩ :=
    WilliamsonShmoys.planar_drawing_triangulation_completion_retry3_exists_maximal_drawable_supergraph
      K hDraw
  obtain ⟨f, hEuler, hIncidence⟩ :=
    WilliamsonShmoys.planar_drawing_triangulation_completion_retry3_maximal_planar_face_decomposition
      L hLDraw hMax hCard
  refine ⟨L, hKL, hLDraw, ?_⟩
  exact WilliamsonShmoys.planar_drawing_triangulation_completion_retry3_edge_count_from_face_equations
    (Fintype.card V) L.edgeSet.ncard f hCard hEuler hIncidence