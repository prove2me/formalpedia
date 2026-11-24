-- Prove2me | solution 3 for WilliamsonShmoys.maximal_drawable_nonempty_connected__p2m_ea88c89d_48b3_414b_a3f4_04bcb156f9eb_a1
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T05:41:15.294114+00:00
-- url     : https://prove2.me/submissions/6a1cd329-7180-4314-926f-ae3f77088468

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
    (K : SimpleGraph V)
    (hV : 1 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax :
      ∀ M : SimpleGraph V,
        K.edgeSet ⊆ M.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn M →
        M.edgeSet ⊆ K.edgeSet) :
    K.Connected := by
  haveI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  by_contra hdis
  obtain ⟨a, b, hab⟩ : ∃ a b, ¬ K.Reachable a b := by
      by_contra hc
      push_neg at hc
      exact hdis ⟨hc⟩
  obtain ⟨M, hKM, hM⟩ := WilliamsonShmoys.planar_drawing_add_edge_for_unreachable_pair__p2m_70e8c091_7bdb_4671_99d7_abbf72db95dd_a1 K hK a b hab
  exact hKM.ne (le_antisymm hKM.le (SimpleGraph.edgeSet_subset_edgeSet.mp (hmax M (SimpleGraph.edgeSet_subset_edgeSet.mpr hKM.le) hM)))
