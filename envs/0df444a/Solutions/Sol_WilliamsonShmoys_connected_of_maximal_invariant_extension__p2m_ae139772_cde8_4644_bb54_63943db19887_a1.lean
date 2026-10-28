-- Prove2me | solution 1 for WilliamsonShmoys.connected_of_maximal_invariant_extension__p2m_ae139772_cde8_4644_bb54_63943db19887_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T20:19:02.865645+00:00
-- url     : https://prove2.me/submissions/1a992714-c98d-4a8a-84e8-91adf5dc8bc4

import Mathlib
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (P : SimpleGraph V → Prop)
    (step : ∀ (G : SimpleGraph V), P G → ¬ G.Connected →
      ∃ K : SimpleGraph V, G ≤ K ∧ P K ∧
        ∃ u v : V, ¬ G.Reachable u v ∧ K.Adj u v)
    (H : SimpleGraph V) (hH : P H)
    (hmax : ∀ K : SimpleGraph V, H ≤ K → P K → K = H) :
    H.Connected := by
  by_contra hconn
  obtain ⟨K, hHK, hPK, u, v, hnot, hAdj⟩ := step H hH hconn
  have hEq : K = H := hmax K hHK hPK
  subst K
  exact hnot hAdj.reachable