-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_face_decomposition__p2m_2f707832_942f_4ae9_9944_7f0d941152ce_a1
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T05:41:12.192879+00:00
-- url     : https://prove2.me/submissions/8bddfd9f-7f11-4bdb-81a6-9265805c7245

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
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K.edgeSet ⊂ L.edgeSet →
      ¬ WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f = K.edgeSet.ncard + 2 ∧
      3 * f = 2 * K.edgeSet.ncard := by
  have hMax' : ∀ J : SimpleGraph _, K ≤ J → HasPlanarDrawingOn J → J ≤ K := by
    intro J hHJ hJ
    by_contra hn
    apply hmax J _ hJ
    refine HasSubset.Subset.ssubset_of_ne (SimpleGraph.edgeSet_subset_edgeSet.mpr hHJ) ?_
    intro h
    exact hn (SimpleGraph.edgeSet_inj.mp h).ge
  have h := WilliamsonShmoys.maximal_planar_edge_count_for_edge_bound_ef555edc K hV hK hMax'
  exact ⟨2 * Fintype.card V - 4, by omega, by omega⟩
