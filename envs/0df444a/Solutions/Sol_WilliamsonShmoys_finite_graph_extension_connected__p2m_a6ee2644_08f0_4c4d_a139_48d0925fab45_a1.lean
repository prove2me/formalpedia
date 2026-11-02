-- Prove2me | solution 1 for WilliamsonShmoys.finite_graph_extension_connected__p2m_a6ee2644_08f0_4c4d_a139_48d0925fab45_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:20:36.277322+00:00
-- url     : https://prove2.me/submissions/87941388-a365-41f1-bac2-2d403a650445

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (Good : SimpleGraph V → Prop)
    (N : SimpleGraph V)
    (hN : Good N)
    (extend : ∀ (G : SimpleGraph V), Good G → ¬ G.Connected →
      ∃ P : SimpleGraph V, G ≤ P ∧ G ≠ P ∧ Good P) :
    ∃ P : SimpleGraph V, N ≤ P ∧ P.Connected ∧ Good P := by
  classical
  let S : Set (SimpleGraph V) := {G | N ≤ G ∧ Good G}
  have hS_finite : S.Finite := Set.toFinite S
  have hS_nonempty : S.Nonempty := ⟨N, le_rfl, hN⟩
  obtain ⟨P, hP_max⟩ := hS_finite.exists_maximal hS_nonempty
  rcases hP_max.1 with ⟨hNP, hGoodP⟩
  have hP_connected : P.Connected := by
    by_contra hP_disconnected
    obtain ⟨Q, hPQ, hP_ne_Q, hGoodQ⟩ := extend P hGoodP hP_disconnected
    have hQ_mem : Q ∈ S := ⟨hNP.trans hPQ, hGoodQ⟩
    have hPQ_eq : P = Q := hP_max.eq_of_le hQ_mem hPQ
    exact hP_ne_Q hPQ_eq
  exact ⟨P, hNP, hP_connected, hGoodP⟩