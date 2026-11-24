-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawing_pair_extension_cert38ffb807
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T05:06:21.259797+00:00
-- url     : https://prove2.me/submissions/1d2fc5cc-4fc2-4c8b-96dc-b2fc3f606304

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
    (G : SimpleGraph V) (hdraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (u v : V) (huv : u ≠ v)
    (hnot : ¬ Relation.ReflTransGen G.Adj u v) :
    ∃ H : SimpleGraph V, G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      Relation.ReflTransGen H.Adj u v := by
  have hab : ¬ G.Reachable u v := fun h => hnot ((SimpleGraph.reachable_iff_reflTransGen _ _).mp h)
  have hdraw0 := hdraw
  by_cases hV : 3 ≤ Fintype.card V
  · obtain ⟨H0, hGH0, hH0, -, hMax0⟩ := WilliamsonShmoys.exists_maximal_planar_supergraph_for_edge_bound_ef555edc G hdraw
    have hC0 : H0.Connected := WilliamsonShmoys.maximal_planar_drawingOn_connected H0 hH0 hMax0 hV
    exact ⟨H0, hGH0, hH0, (SimpleGraph.reachable_iff_reflTransGen _ _).mp (hC0.preconnected u v)⟩
  · have hne : u ≠ v := by rintro rfl; exact hab (SimpleGraph.Reachable.refl _)
    obtain ⟨G', hHG, hG'⟩ := WilliamsonShmoys.planar_drawing_add_edge_for_unreachable_pair__p2m_70e8c091_7bdb_4671_99d7_abbf72db95dd_a1 G hdraw0 u v hab
    obtain ⟨x, y, hG1, hH1⟩ : ∃ x y, G'.Adj x y ∧ ¬ G.Adj x y := by
      by_contra hc
      push_neg at hc
      exact hHG.ne (le_antisymm hHG.le (fun x y h => hc x y h))
    have hall : ∀ w : V, w = u ∨ w = v := by
      intro w
      by_contra hw
      push_neg at hw
      apply hV
      have : ({u, v, w} : Finset V).card = 3 := by
        rw [Finset.card_insert_of_notMem, Finset.card_pair (Ne.symm hw.2)]
        simp [hne, Ne.symm hw.1]
      calc 3 = ({u, v, w} : Finset V).card := this.symm
        _ ≤ Fintype.card V := Finset.card_le_univ _
    have hxy := hG1.ne
    refine ⟨G', hHG.le, hG', (SimpleGraph.reachable_iff_reflTransGen _ _).mp ?_⟩
    rcases hall x with rfl | rfl <;> rcases hall y with rfl | rfl
    · exact absurd rfl hxy
    · exact hG1.reachable
    · exact hG1.reachable.symm
    · exact absurd rfl hxy
