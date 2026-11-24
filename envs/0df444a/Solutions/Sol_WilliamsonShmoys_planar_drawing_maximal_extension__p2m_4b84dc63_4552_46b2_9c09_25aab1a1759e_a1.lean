-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_extension__p2m_4b84dc63_4552_46b2_9c09_25aab1a1759e_a1
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T04:50:57.307253+00:00
-- url     : https://prove2.me/submissions/f5801b61-4108-49b2-bd92-7293f6c4cbf8

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_ef555edc
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawingOn_connected
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_for_edge_bound_ef555edc
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_for_edge_bound_ef555edc
import Theorems.Thm_WilliamsonShmoys_planar_edge_extension_of_disconnected_drawing
import Theorems.Thm_WilliamsonShmoys_planar_drawing_extension_for_edge_bound_ef555edc

set_option autoImplicit false
open WilliamsonShmoys
open scoped BigOperators

theorem solution {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H) (hV : 3 ≤ Fintype.card V) : ∃ K : SimpleGraph V, H.edgeSet ⊆ K.edgeSet ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧ H.edgeSet.ncard ≤ K.edgeSet.ncard ∧ ∀ L : SimpleGraph V, K.edgeSet ⊆ L.edgeSet → WilliamsonShmoys.HasPlanarDrawingOn L → L.edgeSet = K.edgeSet := by
  obtain ⟨K, hHK, hK, hle, hMax0⟩ := WilliamsonShmoys.exists_maximal_planar_supergraph_for_edge_bound_ef555edc H hDraw
  refine ⟨K, SimpleGraph.edgeSet_subset_edgeSet.mpr hHK, hK, hle, ?_⟩
  intro L hKL hL
  have h1 : K ≤ L := SimpleGraph.edgeSet_subset_edgeSet.mp hKL
  exact congrArg SimpleGraph.edgeSet (le_antisymm (hMax0 L h1 hL) h1)
