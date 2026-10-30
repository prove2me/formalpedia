-- Prove2me | solution 1 for WilliamsonShmoys.finite_property_connected_extension__p2m_c5002bd9_287e_4c4a_8f25_d9d45db0800d_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:23:55.586821+00:00
-- url     : https://prove2.me/submissions/dc334700-60ec-49b3-b2d7-e6430f49f876

import Mathlib
import Theorems.Thm_WilliamsonShmoys_exists_edge_card_maximal_property_supergraph__p2m_eb929d3d_412f_49f7_ad86_3f0f4e3e928c_a1
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] (T : SimpleGraph V)
    (P : SimpleGraph V → Prop) (hT : P T)
    (hstep : ∀ G : SimpleGraph V, P G → ¬ G.Connected →
      ∃ H : SimpleGraph V, G.edgeSet ⊆ H.edgeSet ∧ P H ∧
        Nat.card G.edgeSet < Nat.card H.edgeSet) :
    ∃ H : SimpleGraph V, T.edgeSet ⊆ H.edgeSet ∧ P H ∧ H.Connected := by
  obtain ⟨G, hTG, hPG, hmax⟩ :=
    WilliamsonShmoys.exists_edge_card_maximal_property_supergraph__p2m_eb929d3d_412f_49f7_ad86_3f0f4e3e928c_a1 T P hT
  refine ⟨G, hTG, hPG, ?_⟩
  by_contra hconn
  obtain ⟨H, hGH, hPH, hcard⟩ := hstep G hPG hconn
  exact hmax H hGH hPH hcard