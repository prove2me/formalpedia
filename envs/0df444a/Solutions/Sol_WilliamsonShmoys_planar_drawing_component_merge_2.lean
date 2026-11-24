-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawing_component_merge
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T05:41:19.07487+00:00
-- url     : https://prove2.me/submissions/a2a3d379-1c85-4363-a8ac-56bfd7d35e20

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_ef555edc
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawingOn_connected
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_for_edge_bound_ef555edc
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_for_edge_bound_ef555edc
import Theorems.Thm_WilliamsonShmoys_planar_edge_extension_of_disconnected_drawing
import Theorems.Thm_WilliamsonShmoys_planar_drawing_extension_for_edge_bound_ef555edc
import Theorems.Thm_WilliamsonShmoys_planar_drawing_add_edge_for_unreachable_pair__p2m_70e8c091_7bdb_4671_99d7_abbf72db95dd_a1
import Theorems.Thm_WilliamsonShmoys_exists_connected_supergraph_of_strict_extension

set_option autoImplicit false
open WilliamsonShmoys
open scoped BigOperators

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (Y : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hY : WilliamsonShmoys.HasPlanarDrawingOn Y)
    (hDisconnected : ¬ Y.Connected)
    (iY : Fintype Y.ConnectedComponent) :
    ∃ (Z : SimpleGraph V), ∃ (iZ : Fintype Z.ConnectedComponent),
      Y ≤ Z ∧ WilliamsonShmoys.HasPlanarDrawingOn Z ∧
        @Fintype.card Z.ConnectedComponent iZ <
          @Fintype.card Y.ConnectedComponent iY := by
  obtain ⟨H0, hGH0, hH0, -, hMax0⟩ := WilliamsonShmoys.exists_maximal_planar_supergraph_for_edge_bound_ef555edc Y hY
  have hC0 : H0.Connected := WilliamsonShmoys.maximal_planar_drawingOn_connected H0 hH0 hMax0 hV
  haveI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨a, b, hab⟩ : ∃ a b, ¬ Y.Reachable a b := by
      by_contra hc
      push_neg at hc
      exact hDisconnected ⟨hc⟩
  haveI : Subsingleton H0.ConnectedComponent := hC0.preconnected.subsingleton_connectedComponent
  let iZ : Fintype H0.ConnectedComponent := Fintype.ofFinite _
  refine ⟨H0, iZ, hGH0, hH0, ?_⟩
  have h1 : @Fintype.card H0.ConnectedComponent iZ ≤ 1 := Fintype.card_le_one_iff_subsingleton.mpr inferInstance
  have h2 : 1 < @Fintype.card Y.ConnectedComponent iY := by
    rw [Fintype.one_lt_card_iff]
    exact ⟨Y.connectedComponentMk a, Y.connectedComponentMk b, fun h => hab (SimpleGraph.ConnectedComponent.eq.mp h)⟩
  omega
