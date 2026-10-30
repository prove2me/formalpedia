-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_connected_completion_from_bridge_property__p2m_e87f3d6d_f5ac_4caa_95af_19e806d71ee4_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:48:39.771527+00:00
-- url     : https://prove2.me/submissions/c5085a5f-fbf2-414d-b349-3a62f77f7fc2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_WilliamsonShmoys_finite_bridge_completion_sequence__p2m_39b2e6d4_604e_4f41_9365_8bd67e4be3f2_a1
import Theorems.Thm_WilliamsonShmoys_bridge_sequence_preserves_property__p2m_39b2e6d4_604e_4f41_9365_8bd67e4be3f2_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (P : SimpleGraph V → Prop)
    (hP : P M)
    (hne : Nonempty V)
    (hbridge : ∀ (G : SimpleGraph V), P G →
      ∀ x y : V, ¬ G.Reachable x y →
        ∃ N : SimpleGraph V,
          G ≤ N ∧
          (∀ u v, N.Adj u v ↔
            G.Adj u v ∨ ((u = x ∧ v = y) ∨ (u = y ∧ v = x))) ∧
          P N) :
    ∃ N : SimpleGraph V,
      M ≤ N ∧ (∀ x y, N.Reachable x y) ∧ P N := by
  obtain ⟨n, f, hstart, hconnected, hstep⟩ :=
    WilliamsonShmoys.finite_bridge_completion_sequence__p2m_39b2e6d4_604e_4f41_9365_8bd67e4be3f2_a1 M
  obtain ⟨hle, hfinal⟩ :=
    WilliamsonShmoys.bridge_sequence_preserves_property__p2m_39b2e6d4_604e_4f41_9365_8bd67e4be3f2_a1
      M P hP hbridge n f hstart hstep
  exact ⟨f (Fin.last n), hle, hconnected, hfinal⟩