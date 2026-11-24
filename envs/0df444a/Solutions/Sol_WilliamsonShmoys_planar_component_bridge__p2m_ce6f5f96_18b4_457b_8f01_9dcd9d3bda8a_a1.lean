-- Prove2me | solution 1 for WilliamsonShmoys.planar_component_bridge__p2m_ce6f5f96_18b4_457b_8f01_9dcd9d3bda8a_a1
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T04:47:38.831725+00:00
-- url     : https://prove2.me/submissions/a7239a6b-c7d7-48e5-9c21-93d94bbb0072

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
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hDisconnected : ¬ K.Connected) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧ K.edgeSet ⊂ L.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn L := by
  obtain ⟨J, h1, h2, h3⟩ := WilliamsonShmoys.planar_edge_extension_of_disconnected_drawing K hK hV hDisconnected
  refine ⟨J, h1, ?_, h3⟩
  exact HasSubset.Subset.ssubset_of_ne (SimpleGraph.edgeSet_subset_edgeSet.mpr h1) (fun h => h2 (SimpleGraph.edgeSet_inj.mp h).symm)
