-- Prove2me | solution 1 for WilliamsonShmoys.finite_graph_completion_from_steps__p2m_0ac1f81c_3fb8_44a1_92c7_855048ff841d_a4
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-16T15:25:49.926324+00:00
-- url     : https://prove2.me/submissions/b872eb32-d61b-427d-910f-5538b3cb6b4e

import Mathlib

theorem solution {V : Type} [Fintype V] [DecidableEq V]
    (K : SimpleGraph V) (P : SimpleGraph V → Prop)
    (hP : P K)
    (step : ∀ G : SimpleGraph V,
      K ≤ G →
      (∀ x y : V, G.Adj x y → K.Adj x y ∨ ¬ K.Reachable x y) →
      P G → ¬ G.Connected →
      ∃ H : SimpleGraph V,
        G ≤ H ∧ P H ∧
        (∀ x y : V, H.Adj x y → G.Adj x y ∨ ¬ K.Reachable x y) ∧
        ∃ u v : V, ¬ G.Adj u v ∧ H.Adj u v)
    (hNotConnected : ¬ K.Connected) :
    ∃ H : SimpleGraph V,
      K ≤ H ∧ P H ∧ H.Connected ∧
      ∀ x y : V, H.Adj x y → K.Adj x y ∨ ¬ K.Reachable x y := by
  classical
  haveI hfin : Finite (Sym2 V) := Finite.of_fintype _
  set N : ℕ := Nat.card (Sym2 V) with hN
  have hlt : ∀ (G H : SimpleGraph V), G ≤ H → ∀ u v : V, ¬ G.Adj u v → H.Adj u v →
      Nat.card G.edgeSet < Nat.card H.edgeSet := by
    intro G H hGH u v hnadj hadj
    haveI h1 : Fintype G.edgeSet := Fintype.ofFinite _
    haveI h2 : Fintype H.edgeSet := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet,
      SimpleGraph.card_edgeSet]
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset (SimpleGraph.edgeFinset_mono hGH)]
    refine ⟨Sym2.mk u v, ?_, ?_⟩
    · rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      exact hadj
    · rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      exact hnadj
  have hcardN : ∀ G : SimpleGraph V, Nat.card G.edgeSet ≤ N := by
    intro G
    rw [hN]
    exact Nat.card_le_card_of_injective (fun e => (e : Sym2 V)) (fun a b h => Subtype.ext h)
  have key : ∀ k : ℕ, ∀ G : SimpleGraph V, K ≤ G →
      (∀ x y : V, G.Adj x y → K.Adj x y ∨ ¬ K.Reachable x y) → P G →
      N - Nat.card G.edgeSet ≤ k →
      ∃ H : SimpleGraph V, G ≤ H ∧ P H ∧ H.Connected ∧
        ∀ x y : V, H.Adj x y → K.Adj x y ∨ ¬ K.Reachable x y := by
    intro k
    induction k with
    | zero =>
      intro G hKG hinv hPG hk
      by_cases hconn : G.Connected
      · exact ⟨G, le_rfl, hPG, hconn, hinv⟩
      · obtain ⟨H, hGH, hPH, hinvH, u, v, hnadj, hadj⟩ := step G hKG hinv hPG hconn
        have hlt' := hlt G H hGH u v hnadj hadj
        have hNG := hcardN G
        have hNH := hcardN H
        omega
    | succ k ih =>
      intro G hKG hinv hPG hk
      by_cases hconn : G.Connected
      · exact ⟨G, le_rfl, hPG, hconn, hinv⟩
      · obtain ⟨H, hGH, hPH, hinvH, u, v, hnadj, hadj⟩ := step G hKG hinv hPG hconn
        have hlt' := hlt G H hGH u v hnadj hadj
        have hNG := hcardN G
        have hNH := hcardN H
        have hinvH' : ∀ x y : V, H.Adj x y → K.Adj x y ∨ ¬ K.Reachable x y := by
          intro x y hxy
          rcases hinvH x y hxy with h | h
          · exact hinv x y h
          · exact Or.inr h
        have hKH : K ≤ H := le_trans hKG hGH
        obtain ⟨H1, hHH1, hPH1, hconn1, hinv1⟩ := ih H hKH hinvH' hPH (by omega)
        exact ⟨H1, le_trans hGH hHH1, hPH1, hconn1, hinv1⟩
  exact key N K le_rfl (fun x y h => Or.inl h) hP (by omega)
