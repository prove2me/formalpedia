-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count_730ed87f_4857_4202_bf37_5fbad1be2596
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T15:28:58.417213+00:00
-- url     : https://prove2.me/submissions/fa3d3f9f-947a-4ac9-a880-7db8fecb1d71

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_upper_bound_via_face_count
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_lower_bound_via_triangulation

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hT : WilliamsonShmoys.HasPlanarDrawingOn T)
    (hmax : ∀ U : SimpleGraph V, T ≤ U →
      WilliamsonShmoys.HasPlanarDrawingOn U → U = T) :
    T.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hupper := WilliamsonShmoys.planar_drawing_edge_count_upper_bound_via_face_count
    T hV hT
  have hlower := WilliamsonShmoys.maximal_planar_drawing_edge_count_lower_bound_via_triangulation
    T hV hT hmax
  omega
