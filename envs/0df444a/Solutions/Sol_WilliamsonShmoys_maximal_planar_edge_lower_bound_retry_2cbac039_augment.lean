-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_lower_bound_retry_2cbac039_augment
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T04:50:58.076684+00:00
-- url     : https://prove2.me/submissions/f3b9e69b-b17d-4569-81d2-9ef0bf707c3d

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

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V)
    (hSparse : L.edgeSet.ncard + 6 < 3 * Fintype.card V) :
    ∃ M : SimpleGraph V, WilliamsonShmoys.HasPlanarDrawingOn M ∧
      L.edgeSet ⊂ M.edgeSet := by
  obtain ⟨H0, hLH0, hH0, -, hMax0⟩ := WilliamsonShmoys.exists_maximal_planar_supergraph_for_edge_bound_ef555edc L hL
  have h := WilliamsonShmoys.maximal_planar_edge_count_for_edge_bound_ef555edc H0 hCard hH0 hMax0
  refine ⟨H0, hH0, HasSubset.Subset.ssubset_of_ne (SimpleGraph.edgeSet_subset_edgeSet.mpr hLH0) ?_⟩
  intro hEq
  rw [hEq] at hSparse
  omega
