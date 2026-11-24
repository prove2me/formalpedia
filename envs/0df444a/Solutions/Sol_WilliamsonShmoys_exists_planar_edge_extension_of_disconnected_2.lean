-- Prove2me | solution 2 for WilliamsonShmoys.exists_planar_edge_extension_of_disconnected
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T05:03:35.063237+00:00
-- url     : https://prove2.me/submissions/a6dec442-82a4-482f-a42b-87a4e9e8f042

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
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V)
    (hDisconnected : ¬ G.Connected) :
    ∃ K : SimpleGraph V, G ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∃ u v : V, ¬ G.Reachable u v ∧ K.Adj u v := by
  obtain ⟨H0, hGH0, hH0, hle0, hMax0⟩ := WilliamsonShmoys.exists_maximal_planar_supergraph_for_edge_bound_ef555edc G hG
  have hC0 : H0.Connected := WilliamsonShmoys.maximal_planar_drawingOn_connected H0 hH0 hMax0 hCard
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
  haveI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨a, b, hab⟩ : ∃ a b, ¬ G.Reachable a b := by
    by_contra hc
    push_neg at hc
    exact hDisconnected ⟨hc⟩
  obtain ⟨u, v, h1, h2⟩ := cross a b (hC0.preconnected a b).some hab
  exact ⟨H0, hGH0, hH0, u, v, h1, h2⟩
