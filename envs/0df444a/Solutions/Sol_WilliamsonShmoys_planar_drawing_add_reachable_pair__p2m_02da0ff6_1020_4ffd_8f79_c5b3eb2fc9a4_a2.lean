-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_add_reachable_pair__p2m_02da0ff6_1020_4ffd_8f79_c5b3eb2fc9a4_a2
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T05:03:37.448916+00:00
-- url     : https://prove2.me/submissions/be9bf8e9-0af3-4b09-a970-c9e74013f653

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_ef555edc
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawingOn_connected
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_for_edge_bound_ef555edc
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_for_edge_bound_ef555edc
import Theorems.Thm_WilliamsonShmoys_planar_edge_extension_of_disconnected_drawing
import Theorems.Thm_WilliamsonShmoys_planar_drawing_extension_for_edge_bound_ef555edc
import Theorems.Thm_WilliamsonShmoys_planar_drawing_add_edge_for_unreachable_pair__p2m_70e8c091_7bdb_4671_99d7_abbf72db95dd_a1

set_option autoImplicit false
open WilliamsonShmoys
open scoped BigOperators

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hH : HasPlanarDrawingOn H) {a b : V}
    (hab : ¬ H.Reachable a b) :
    ∃ G : SimpleGraph V, H ≤ G ∧ HasPlanarDrawingOn G ∧ G.Reachable a b := by
  by_cases hV : 3 ≤ Fintype.card V
  · obtain ⟨H0, hGH0, hH0, hle0, hMax0⟩ := WilliamsonShmoys.exists_maximal_planar_supergraph_for_edge_bound_ef555edc H hH
    have hC0 : H0.Connected := WilliamsonShmoys.maximal_planar_drawingOn_connected H0 hH0 hMax0 hV
    exact ⟨H0, hGH0, hH0, hC0.preconnected a b⟩
  · have hne : a ≠ b := by rintro rfl; exact hab (SimpleGraph.Reachable.refl a)
    obtain ⟨G, hHG, hG⟩ := WilliamsonShmoys.planar_drawing_add_edge_for_unreachable_pair__p2m_70e8c091_7bdb_4671_99d7_abbf72db95dd_a1 H hH a b hab
    obtain ⟨x, y, hG1, hH1⟩ : ∃ x y, G.Adj x y ∧ ¬ H.Adj x y := by
      by_contra hc
      push_neg at hc
      exact hHG.ne (le_antisymm hHG.le (fun x y h => hc x y h))
    have hall : ∀ w : V, w = a ∨ w = b := by
      intro w
      by_contra hw
      push_neg at hw
      apply hV
      have : ({a, b, w} : Finset V).card = 3 := by
        rw [Finset.card_insert_of_notMem, Finset.card_pair (Ne.symm hw.2)]
        simp [hne, Ne.symm hw.1]
      calc 3 = ({a, b, w} : Finset V).card := this.symm
        _ ≤ Fintype.card V := Finset.card_le_univ _
    have hxy := hG1.ne
    refine ⟨G, hHG.le, hG, ?_⟩
    rcases hall x with rfl | rfl <;> rcases hall y with rfl | rfl
    · exact absurd rfl hxy
    · exact hG1.reachable
    · exact hG1.reachable.symm
    · exact absurd rfl hxy
