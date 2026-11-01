-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_cut_bridge__p2m_0b5c6abe_9063_498b_b66b_6e8d4f2b2880_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:03:09.387036+00:00
-- url     : https://prove2.me/submissions/51a42d5e-1be4-4bc1-a050-fa39cbc326ba
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_cut_separates_reachable__p2m_9a2bae5c_cda3_4fda_a7e2_a764b5d323bb_a1
import Theorems.Thm_WilliamsonShmoys_planar_drawing_bridge_disconnected__p2m_9a2bae5c_cda3_4fda_a7e2_a764b5d323bb_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (S : Set V) (u v : V)
    (hu : u ∈ S) (hv : v ∉ S)
    (hcut : ∀ ⦃a b : V⦄, a ∈ S → b ∉ S → ¬ G.Adj a b) :
    ∃ H : SimpleGraph V,
      (∀ a b, H.Adj a b ↔
        G.Adj a b ∨ ((a = u ∧ b = v) ∨ (a = v ∧ b = u))) ∧
      WilliamsonShmoys.HasPlanarDrawingOn H := by
  have hdisconnected : ¬ G.Reachable u v :=
    WilliamsonShmoys.cut_separates_reachable__p2m_9a2bae5c_cda3_4fda_a7e2_a764b5d323bb_a1
      G S u v hu hv hcut
  exact WilliamsonShmoys.planar_drawing_bridge_disconnected__p2m_9a2bae5c_cda3_4fda_a7e2_a764b5d323bb_a1
    G hG u v hdisconnected