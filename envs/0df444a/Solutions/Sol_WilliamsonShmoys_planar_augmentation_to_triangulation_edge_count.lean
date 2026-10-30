-- Prove2me | solution 1 for WilliamsonShmoys.planar_augmentation_to_triangulation_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-25T23:54:28.390885+00:00
-- url     : https://prove2.me/submissions/60ca4c8c-ca8e-4e5a-9741-0f1acea8502a

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_edge_maximal_extension
import Theorems.Thm_WilliamsonShmoys_edge_count_of_edge_maximal_planar_drawing

set_option autoImplicit false

 theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V, K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
      L.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨L, hKL, hL, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_has_edge_maximal_extension K hV hK
  have hcount := WilliamsonShmoys.edge_count_of_edge_maximal_planar_drawing
    L hV hL hmax
  exact ⟨L, hKL, hL, hcount⟩