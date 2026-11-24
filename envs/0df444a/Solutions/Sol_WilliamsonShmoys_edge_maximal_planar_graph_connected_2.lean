-- Prove2me | solution 2 for WilliamsonShmoys.edge_maximal_planar_graph_connected
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T04:51:02.652929+00:00
-- url     : https://prove2.me/submissions/1e68cc5e-6e54-42d5-9387-ac5a2f8a54f5

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
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ K : SimpleGraph V,
      (∀ ⦃u v⦄, H.Adj u v → K.Adj u v) →
      WilliamsonShmoys.HasPlanarDrawingOn K →
      K.edgeSet.ncard ≤ H.edgeSet.ncard) :
    ∀ u v, Relation.ReflTransGen H.Adj u v := by
  have hMax' : ∀ J : SimpleGraph _, H ≤ J → HasPlanarDrawingOn J → J ≤ H := by
    intro J hHJ hJ
    have hsub := SimpleGraph.edgeSet_subset_edgeSet.mpr hHJ
    have hle := hmax J (fun u v h => hHJ h) hJ
    exact (SimpleGraph.edgeSet_inj.mp (Set.eq_of_subset_of_ncard_le hsub hle (Set.toFinite _)).symm).le
  have hC := WilliamsonShmoys.maximal_planar_drawingOn_connected H hH hMax' hV
  intro u v
  exact (SimpleGraph.reachable_iff_reflTransGen _ _).mp (hC.preconnected u v)
