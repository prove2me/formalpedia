-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawing_connected_supergraph__p2m_03ccc876_b6bf_43b7_928a_d41b56ffed25_a1
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T05:41:14.129561+00:00
-- url     : https://prove2.me/submissions/febe427c-3431-456e-bfdb-510fadce9a0e

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
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
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ (K : SimpleGraph V) (_ : DecidableRel K.Adj),
      H.edgeFinset ⊆ K.edgeFinset ∧
      K.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn K := by
  classical
  haveI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨C, hGC, ⟨-, hC⟩, hconnC⟩ := WilliamsonShmoys.exists_connected_supergraph_of_strict_extension H
    (fun X0 => H ≤ X0 ∧ WilliamsonShmoys.HasPlanarDrawingOn X0) ⟨le_rfl, hH⟩ (by
      rintro X0 - ⟨hGX, hX⟩ hnc
      obtain ⟨a, b, hab⟩ : ∃ a b, ¬ X0.Reachable a b := by
        by_contra hc
        push_neg at hc
        exact hnc ⟨hc⟩
      obtain ⟨K1, hXK, hK1⟩ := WilliamsonShmoys.planar_drawing_add_edge_for_unreachable_pair__p2m_70e8c091_7bdb_4671_99d7_abbf72db95dd_a1 X0 hX a b hab
      exact ⟨K1, hXK, hGX.trans hXK.le, hK1⟩)
  exact ⟨C, Classical.decRel _, SimpleGraph.edgeFinset_subset_edgeFinset.mpr hGC, hconnC, hC⟩
