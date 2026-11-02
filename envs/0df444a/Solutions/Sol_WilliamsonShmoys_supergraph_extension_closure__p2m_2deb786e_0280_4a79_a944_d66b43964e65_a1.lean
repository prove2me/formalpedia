-- Prove2me | solution 1 for WilliamsonShmoys.supergraph_extension_closure__p2m_2deb786e_0280_4a79_a944_d66b43964e65_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T06:49:22.810247+00:00
-- url     : https://prove2.me/submissions/53f4ca4f-0f35-4332-998a-c6d3c6103e94

import Mathlib
set_option autoImplicit false

open SimpleGraph

theorem solution
    {V : Type} [Fintype V]
    (P : SimpleGraph V → Prop) (G : SimpleGraph V) (hP : P G)
    (hstep : ∀ K : SimpleGraph V, P K → ¬ K.Connected →
      ∃ H : SimpleGraph V,
        (∀ u v, K.Adj u v → H.Adj u v) ∧
        (∃ u v, ¬ K.Adj u v ∧ H.Adj u v) ∧ P H) :
    ∃ H : SimpleGraph V,
      (∀ u v, G.Adj u v → H.Adj u v) ∧ H.Connected ∧ P H := by
  classical
  let M : ℕ := (⊤ : SimpleGraph V).edgeFinset.card
  have aux : ∀ n (K : SimpleGraph V),
      M - K.edgeFinset.card = n → G ≤ K → P K →
      ∃ H : SimpleGraph V,
        (∀ u v, G.Adj u v → H.Adj u v) ∧ H.Connected ∧ P H := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro K hmeasure hGK hPK
      by_cases hconn : K.Connected
      · exact ⟨K, (fun u v huv => hGK huv), hconn, hPK⟩
      · obtain ⟨H, hsub, hextra, hPH⟩ := hstep K hPK hconn
        have hKH : K ≤ H := by
          intro u v huv
          exact hsub u v huv
        have hstrict : K < H := by
          apply lt_of_le_of_ne hKH
          intro heq
          rcases hextra with ⟨u, v, hnot, hadj⟩
          apply hnot
          have : K.Adj u v := by simpa [heq] using hadj
          exact this
        have hcard : K.edgeFinset.card < H.edgeFinset.card :=
          Finset.card_lt_card ((SimpleGraph.edgeFinset_ssubset_edgeFinset).2 hstrict)
        have hHle : H.edgeFinset.card ≤ M := by
          dsimp [M]
          exact Finset.card_le_card (SimpleGraph.edgeFinset_mono le_top)
        have hdecrease : M - H.edgeFinset.card < n := by
          rw [← hmeasure]
          omega
        have hGH : G ≤ H := le_trans hGK hKH
        obtain ⟨J, hGJ, hJconn, hPJ⟩ :=
          ih (M - H.edgeFinset.card) hdecrease H rfl hGH hPH
        exact ⟨J, hGJ, hJconn, hPJ⟩
  exact aux (M - G.edgeFinset.card) G rfl le_rfl hP