-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_augmentation_bound_same_vertices
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T06:56:22.511214+00:00
-- url     : https://prove2.me/submissions/6fe3abd7-8568-45d5-b2a0-56b1b4f1701b

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawingOn_maximal_supergraph_exists_same_vertices
import Theorems.Thm_WilliamsonShmoys_planar_drawingOn_edge_maximal_supergraph_edge_bound

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (hCard : 3 <= Fintype.card V) :
    ∃ K : SimpleGraph V, HasPlanarDrawingOn K ∧ G ≤ K ∧
      3 * (Fintype.card V : Int) - 6 <= (K.edgeSet.ncard : Int) := by
  obtain ⟨K, hK, hGK, hmax⟩ :=
    WilliamsonShmoys.planar_drawingOn_maximal_supergraph_exists_same_vertices G hG
  refine ⟨K, hK, hGK, ?_⟩
  exact WilliamsonShmoys.planar_drawingOn_edge_maximal_supergraph_edge_bound K hK hCard hmax