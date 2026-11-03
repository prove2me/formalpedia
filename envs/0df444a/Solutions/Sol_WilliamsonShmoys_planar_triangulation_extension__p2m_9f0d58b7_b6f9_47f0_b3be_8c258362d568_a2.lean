-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_extension__p2m_9f0d58b7_b6f9_47f0_b3be_8c258362d568_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-02T16:19:44.860442+00:00
-- url     : https://prove2.me/submissions/b95a9230-5c8c-4ab0-b17f-594b4758e31f

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_98d2ce50_16ca_4db3_bebc_b1953e5d6a1b_a1
import Theorems.Thm_WilliamsonShmoys_maximal_drawing_edge_count_lower__p2m_9c5c2913_8662_47f3_b676_c48b7de0b279_a1
import Theorems.Thm_WilliamsonShmoys_planar_graph_edge_count_upper_bound_dabb2cbe_7fe3_4213_96ba_204afbbd922b

set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hplanar : HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V, H ≤ K ∧ HasPlanarDrawingOn K ∧
      3 * Fintype.card V = K.edgeSet.ncard + 6 := by
  obtain ⟨K, hHK, hK, hmax⟩ :=
    planar_drawing_maximal_extension__p2m_98d2ce50_16ca_4db3_bebc_b1953e5d6a1b_a1 H hplanar
  refine ⟨K, hHK, hK, le_antisymm ?_ ?_⟩
  · exact maximal_drawing_edge_count_lower__p2m_9c5c2913_8662_47f3_b676_c48b7de0b279_a1 K hK hmax hcard
  · exact planar_graph_edge_count_upper_bound_dabb2cbe_7fe3_4213_96ba_204afbbd922b K hcard hK