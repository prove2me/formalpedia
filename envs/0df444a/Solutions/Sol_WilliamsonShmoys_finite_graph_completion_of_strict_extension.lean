-- Prove2me | solution 1 for WilliamsonShmoys.finite_graph_completion_of_strict_extension
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T05:26:47.205253+00:00
-- url     : https://prove2.me/submissions/8216f538-d17c-4d27-b201-475f290cb623

import Mathlib

theorem solution
    {V : Type} [Fintype V]
    (P : SimpleGraph V → Prop)
    (hstep : ∀ (G : SimpleGraph V), P G → ¬ G.Connected →
      ∃ H : SimpleGraph V,
        G ≤ H ∧ G.edgeSet.ncard < H.edgeSet.ncard ∧ P H)
    (R : SimpleGraph V)
    (hR : P R) :
    ∃ S : SimpleGraph V,
      R.edgeSet.ncard ≤ S.edgeSet.ncard ∧
      S.Connected ∧ P S := by
  let N : ℕ := Nat.card (Sym2 V)
  have edge_bound (G : SimpleGraph V) : G.edgeSet.ncard ≤ N := by
    dsimp [N]
    exact Set.ncard_le_card G.edgeSet
  have aux : ∀ n : ℕ, ∀ G : SimpleGraph V,
      N - G.edgeSet.ncard = n → P G →
      ∃ S : SimpleGraph V, G ≤ S ∧ S.Connected ∧ P S := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro G hmeasure hPG
      by_cases hconn : G.Connected
      · exact ⟨G, le_rfl, hconn, hPG⟩
      · obtain ⟨H, hGH, hlt, hPH⟩ := hstep G hPG hconn
        have hdecr : N - H.edgeSet.ncard < n := by
          rw [← hmeasure]
          have hGbound := edge_bound G
          have hHbound := edge_bound H
          omega
        obtain ⟨S, hHS, hSconn, hPS⟩ :=
          ih (N - H.edgeSet.ncard) hdecr H rfl hPH
        exact ⟨S, hGH.trans hHS, hSconn, hPS⟩
  obtain ⟨S, hRS, hSconn, hPS⟩ :=
    aux (N - R.edgeSet.ncard) R rfl hR
  exact ⟨S, Set.ncard_le_ncard (SimpleGraph.edgeSet_mono hRS), hSconn, hPS⟩