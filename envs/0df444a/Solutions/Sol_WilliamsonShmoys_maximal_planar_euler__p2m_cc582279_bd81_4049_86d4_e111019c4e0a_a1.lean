-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_euler__p2m_cc582279_bd81_4049_86d4_e111019c4e0a_a1
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T05:41:11.507187+00:00
-- url     : https://prove2.me/submissions/e1dc4315-7c3f-4430-9c80-84df562c9872

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
    ∃ f : ℕ, Fintype.card V + f = K.edgeSet.ncard + 2 := by
  have hMax' : ∀ J : SimpleGraph _, K ≤ J → HasPlanarDrawingOn J → J ≤ K := by
    intro J hHJ hJ
    by_contra hn
    apply hmax J _ hJ
    refine HasSubset.Subset.ssubset_of_ne (SimpleGraph.edgeSet_subset_edgeSet.mpr hHJ) ?_
    intro h
    exact hn (SimpleGraph.edgeSet_inj.mp h).ge
  have h := WilliamsonShmoys.maximal_planar_edge_count_for_edge_bound_ef555edc K hV hK hMax'
  exact ⟨2 * Fintype.card V - 4, by omega⟩
