-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulation_extension_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T15:40:07.554287+00:00
-- url     : https://prove2.me/submissions/b227ea74-38c4-4d90-bb56-a4900c0a0db2

import Mathlib.Tactic
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_ceaeb6d3_exists_inclusion_maximal_planar_supergraph_finite
import Theorems.Thm_WilliamsonShmoys_ceaeb6d3_maximal_planar_drawing_face_equations

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G.edgeSet ⊆ H.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      (∀ K : SimpleGraph V,
        H.edgeSet ⊆ K.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn K →
        K.edgeSet ⊆ H.edgeSet) ∧
      H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨H, hGH, hH, hMax⟩ :=
    WilliamsonShmoys.ceaeb6d3_exists_inclusion_maximal_planar_supergraph_finite G hG
  obtain ⟨f, hEuler, hFaces⟩ :=
    WilliamsonShmoys.ceaeb6d3_maximal_planar_drawing_face_equations H hH hMax hV
  refine ⟨H, hGH, hH, hMax, ?_⟩
  omega