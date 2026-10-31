-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_lower_of_maximal_drawing__p2m_fcb8ec4c_c30d_44dd_a4d8_def1801ee290_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:05:31.789178+00:00
-- url     : https://prove2.me/submissions/ea1d2f3a-da26-4f34-94f4-080cf90b3ab7

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_completion_edge_count__p2m_b7ddd4a0_5822_4de2_a826_6e2dd80a911f_a1
set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hCard : 3 ≤ Fintype.card V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H) (hmax : ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H) : 3 * Fintype.card V - 6 ≤ H.edgeSet.ncard := by
  obtain ⟨K, hHK, hK, hEdges⟩ := WilliamsonShmoys.planar_triangulation_completion_edge_count__p2m_b7ddd4a0_5822_4de2_a826_6e2dd80a911f_a1 H hCard hH
  have hKH : K = H := hmax K hHK hK
  rw [← hKH]
  exact le_of_eq hEdges.symm