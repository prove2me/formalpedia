-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_bridge_extension__p2m_977ef0e9_2b10_4ce9_abb8_e8741d8c6875_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T20:58:38.235526+00:00
-- url     : https://prove2.me/submissions/ddd6d4f6-ff19-47e3-996f-778b04ba1229
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_reachable_cut_partition__p2m_0b5c6abe_9063_498b_b66b_6e8d4f2b2880_a2
import Theorems.Thm_WilliamsonShmoys_planar_drawing_cut_bridge__p2m_0b5c6abe_9063_498b_b66b_6e8d4f2b2880_a2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (dG : DecidableRel G.Adj)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (u v : V) (hsep : ¬ G.Reachable u v) :
    ∃ H : SimpleGraph V,
      (∀ a b, H.Adj a b ↔
        G.Adj a b ∨ ((a = u ∧ b = v) ∨ (a = v ∧ b = u))) ∧
      WilliamsonShmoys.HasPlanarDrawingOn H := by
  obtain ⟨S, huS, hvS, hcut⟩ :=
    WilliamsonShmoys.reachable_cut_partition__p2m_0b5c6abe_9063_498b_b66b_6e8d4f2b2880_a2
      G u v hsep
  exact WilliamsonShmoys.planar_drawing_cut_bridge__p2m_0b5c6abe_9063_498b_b66b_6e8d4f2b2880_a2
    G hG S u v huS hvS hcut
