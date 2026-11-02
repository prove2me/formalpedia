-- Prove2me | solution 1 for WilliamsonShmoys.finite_connected_closure_of_monotone_step__p2m_5d1dfa1d_991a_49fd_b455_4945d33b9ed1_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T20:44:08.892222+00:00
-- url     : https://prove2.me/submissions/c5e0eb00-aea3-4819-97fc-790d6faa0290

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (P : SimpleGraph V → Prop)
    (hstep : ∀ G : SimpleGraph V, P G → ¬ G.Connected →
      ∃ K : SimpleGraph V,
        G ≤ K ∧ P K ∧
        ∃ u v : V, ¬ G.Reachable u v ∧ K.Reachable u v) :
    ∀ G : SimpleGraph V, P G →
      ∃ K : SimpleGraph V, G ≤ K ∧ K.Connected ∧ P K := by
  classical
  let bad : SimpleGraph V → Finset (V × V) := fun G =>
    Finset.univ.filter (fun p => ¬ G.Reachable p.1 p.2)
  have hclosure : ∀ n : ℕ, ∀ G : SimpleGraph V,
      (bad G).card = n → P G →
      ∃ K : SimpleGraph V, G ≤ K ∧ P K ∧ ∀ u v : V, K.Reachable u v := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro G hcard hPG
      by_cases hall : ∀ u v : V, G.Reachable u v
      · exact ⟨G, le_rfl, hPG, hall⟩
      · have hnot : ¬ G.Connected := by
          intro hconn
          apply hall
          exact hconn.preconnected
        obtain ⟨K, hGK, hPK, u, v, hmiss, hnew⟩ := hstep G hPG hnot
        have hsubset : bad K ⊆ bad G := by
          intro p hp
          have hp' : ¬ K.Reachable p.1 p.2 := (Finset.mem_filter.mp hp).2
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_univ p, ?_⟩
          intro hreach
          exact hp' (SimpleGraph.Reachable.mono hGK hreach)
        have hmemG : (u, v) ∈ bad G := by
          simp [bad, hmiss]
        have hmemK : (u, v) ∉ bad K := by
          simp [bad, hnew]
        have hstrict : bad K ⊂ bad G := by
          apply Finset.ssubset_iff_subset_ne.mpr
          refine ⟨hsubset, ?_⟩
          intro heq
          have hmem : (u, v) ∈ bad K := by
            rw [heq]
            exact hmemG
          exact hmemK hmem
        have hlt : (bad K).card < n := by
          rw [← hcard]
          exact Finset.card_lt_card hstrict
        obtain ⟨L, hKL, hPL, hreachL⟩ := ih (bad K).card hlt K rfl hPK
        exact ⟨L, le_trans hGK hKL, hPL, hreachL⟩
  intro G hG
  have hV : Nonempty V := by
    by_contra hn
    have hnot : ¬ G.Connected := by
      intro hc
      exact hn hc.nonempty
    obtain ⟨K, _hGK, _hPK, u, _v, _hmiss, _hnew⟩ := hstep G hG hnot
    exact hn ⟨u⟩
  letI : Nonempty V := hV
  obtain ⟨K, hGK, hPK, hreach⟩ := hclosure (bad G).card G rfl hG
  exact ⟨K, hGK, ⟨hreach⟩, hPK⟩
