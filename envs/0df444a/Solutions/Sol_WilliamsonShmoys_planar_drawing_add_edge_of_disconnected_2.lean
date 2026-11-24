-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawing_add_edge_of_disconnected
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T05:03:33.568219+00:00
-- url     : https://prove2.me/submissions/9a4576ea-ecf2-4b3a-bfe8-70143f42b5f6

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
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
    (X : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hX : WilliamsonShmoys.HasPlanarDrawingOn X)
    (hDisconnected : ¬ X.Connected) :
    ∃ Z : SimpleGraph V,
      X ≤ Z ∧
      X.edgeSet.ncard < Z.edgeSet.ncard ∧
      WilliamsonShmoys.HasPlanarDrawingOn Z := by
  obtain ⟨J, h1, h2, h3⟩ := WilliamsonShmoys.planar_edge_extension_of_disconnected_drawing X hX hV hDisconnected
  refine ⟨J, h1, ?_, h3⟩
  apply Set.ncard_lt_ncard _ (Set.toFinite _)
  exact HasSubset.Subset.ssubset_of_ne (SimpleGraph.edgeSet_subset_edgeSet.mpr h1) (fun h => h2 (SimpleGraph.edgeSet_inj.mp h).symm)
