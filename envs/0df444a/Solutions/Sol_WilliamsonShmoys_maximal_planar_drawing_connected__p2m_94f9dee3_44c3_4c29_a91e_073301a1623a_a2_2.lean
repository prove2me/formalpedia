-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_drawing_connected__p2m_94f9dee3_44c3_4c29_a91e_073301a1623a_a2
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T05:41:16.608686+00:00
-- url     : https://prove2.me/submissions/c6cfc234-2a4e-4b1e-8cce-212b1b0e8763

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
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ (L : SimpleGraph V) [DecidableRel L.Adj],
      K.edgeFinset ⊆ L.edgeFinset →
      WilliamsonShmoys.HasPlanarDrawingOn L →
      L.edgeFinset ⊆ K.edgeFinset) :
    K.Connected := by
  classical
  haveI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  by_contra hdis
  obtain ⟨a, b, hab⟩ : ∃ a b, ¬ K.Reachable a b := by
      by_contra hc
      push_neg at hc
      exact hdis ⟨hc⟩
  obtain ⟨M, hKM, hM⟩ := WilliamsonShmoys.planar_drawing_add_edge_for_unreachable_pair__p2m_70e8c091_7bdb_4671_99d7_abbf72db95dd_a1 K hK a b hab
  exact hKM.ne (le_antisymm hKM.le (SimpleGraph.edgeFinset_subset_edgeFinset.mp (hmax M (SimpleGraph.edgeFinset_subset_edgeFinset.mpr hKM.le) hM)))
