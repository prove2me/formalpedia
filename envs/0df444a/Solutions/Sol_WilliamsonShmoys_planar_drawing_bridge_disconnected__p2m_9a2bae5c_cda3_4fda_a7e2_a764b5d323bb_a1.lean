-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_bridge_disconnected__p2m_9a2bae5c_cda3_4fda_a7e2_a764b5d323bb_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:08:30.85635+00:00
-- url     : https://prove2.me/submissions/897a6b76-5a43-4dcd-8dc5-ccd18f6896bc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_reachable_component_is_separating__p2m_3eced331_e15d_452f_ac43_a684696313f5_a1
import Theorems.Thm_WilliamsonShmoys_planar_drawing_add_edge_across_separation__p2m_3eced331_e15d_452f_ac43_a684696313f5_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (u v : V)
    (hdisconnected : ¬ G.Reachable u v) :
    ∃ H : SimpleGraph V,
      (∀ a b, H.Adj a b ↔
        G.Adj a b ∨ ((a = u ∧ b = v) ∨ (a = v ∧ b = u))) ∧
      WilliamsonShmoys.HasPlanarDrawingOn H := by
  obtain ⟨A, huA, hvA, hsep⟩ :=
    WilliamsonShmoys.reachable_component_is_separating__p2m_3eced331_e15d_452f_ac43_a684696313f5_a1
      G u v hdisconnected
  exact WilliamsonShmoys.planar_drawing_add_edge_across_separation__p2m_3eced331_e15d_452f_ac43_a684696313f5_a1
    G hG u v A huA hvA hsep