-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_bridge_extension_nonempty__p2m_711af4b4_5214_45eb_bc71_e82c24cc238b_a3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:51:32.546337+00:00
-- url     : https://prove2.me/submissions/071af4e9-5613-4ac3-975f-dfa7d6394d05
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_bridge_extension_fixed_endpoints__p2m_c404492e_8c81_4cec_a5ba_6ddb6067f960_a1
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (hcard : 3 <= Fintype.card V)
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hdisconnected : ¬ G.Connected) :
    ∃ u v : V, ¬ G.Reachable u v ∧
      ∃ P : SimpleGraph V,
        (∀ x y : V, P.Adj x y ↔
          G.Adj x y ∨ ((x = u ∧ y = v) ∨ (x = v ∧ y = u))) ∧
        WilliamsonShmoys.HasPlanarDrawingOn P := by
  classical
  have hV : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  rw [SimpleGraph.connected_iff_exists_forall_reachable] at hdisconnected
  push_neg at hdisconnected
  obtain ⟨u⟩ := hV
  obtain ⟨v, hnot⟩ := hdisconnected u
  obtain ⟨P, hP, hplanar⟩ :=
    WilliamsonShmoys.planar_drawing_bridge_extension_fixed_endpoints__p2m_c404492e_8c81_4cec_a5ba_6ddb6067f960_a1
      G hG u v hnot
  exact ⟨u, v, hnot, P, hP, hplanar⟩