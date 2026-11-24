-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_add_bridge
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T05:06:22.365821+00:00
-- url     : https://prove2.me/submissions/cbb395c5-ccb0-49bf-a11a-9feefb3a7da9

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
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hDisconnected : ¬ (∀ u v : V, Nonempty (G.Walk u v))) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∃ u v : V, ¬ Nonempty (G.Walk u v) ∧ H.Adj u v := by
  have hdraw0 := hG
  obtain ⟨a, b, hab⟩ : ∃ a b, ¬ G.Reachable a b := by
    by_contra hc
    push_neg at hc
    exact hDisconnected (fun u v => hc u v)
  by_cases hV : 3 ≤ Fintype.card V
  · obtain ⟨H0, hGH0, hH0, hle0, hMax0⟩ := WilliamsonShmoys.exists_maximal_planar_supergraph_for_edge_bound_ef555edc G hG
    have hC0 : H0.Connected := WilliamsonShmoys.maximal_planar_drawingOn_connected H0 hH0 hMax0 hV
    have cross : ∀ (a b : V) (w : H0.Walk a b), ¬ G.Reachable a b →
        ∃ u v, ¬ G.Reachable u v ∧ H0.Adj u v := by
      intro a b w
      induction w with
      | nil => intro h; exact absurd (SimpleGraph.Reachable.refl _) h
      | @cons x y z hadj w ih =>
        intro h
        by_cases hxy : G.Reachable x y
        · exact ih (fun hyz => h (hxy.trans hyz))
        · exact ⟨x, y, hxy, hadj⟩
    obtain ⟨u, v, h1, h2⟩ := cross a b (hC0.preconnected a b).some hab
    exact ⟨H0, hGH0, hH0, u, v, h1, h2⟩
  · have hne : a ≠ b := by rintro rfl; exact hab (SimpleGraph.Reachable.refl _)
    obtain ⟨G', hHG, hG'⟩ := WilliamsonShmoys.planar_drawing_add_edge_for_unreachable_pair__p2m_70e8c091_7bdb_4671_99d7_abbf72db95dd_a1 G hdraw0 a b hab
    obtain ⟨x, y, hG1, hH1⟩ : ∃ x y, G'.Adj x y ∧ ¬ G.Adj x y := by
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
    refine ⟨G', hHG.le, hG', ?_⟩
    rcases hall x with rfl | rfl <;> rcases hall y with rfl | rfl
    · exact absurd rfl hxy
    · exact ⟨x, y, hab, hG1⟩
    · exact ⟨y, x, hab, hG1.symm⟩
    · exact absurd rfl hxy
