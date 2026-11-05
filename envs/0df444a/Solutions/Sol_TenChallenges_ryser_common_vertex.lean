-- Prove2me | solution 1 for TenChallenges.ryser_common_vertex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:20:22.530816+00:00
-- url     : https://prove2.me/submissions/52563183-8936-44bd-9d32-f8f7bb33d584

import Definitions.Def_TenChallenges_Challenge_08

/-- Ryser's inequality holds when all edges have a common vertex. -/
theorem solution {V : Type*} [DecidableEq V] (H : FinHypergraph V)
    (r : ℕ) (hr : 2 ≤ r) (v : V) (hv : v ∈ H.vertices)
    (hcommon : ∀ e ∈ H.edges, v ∈ e) : H.RyserConjectureFor r := by
  classical
  intro _ _
  by_cases hne : H.edges.Nonempty
  · obtain ⟨e, he⟩ := hne
    have hcover : H.coverNumber ≤ 1 := by
      apply Nat.sInf_le
      exact ⟨{v}, ⟨by simpa using hv, fun e he => ⟨v, by simp, hcommon e he⟩⟩, by simp⟩
    have hb : BddAbove {n | ∃ M : Finset (Finset V), H.IsMatching M ∧ M.card = n} := by
      refine ⟨H.vertices.powerset.card, ?_⟩
      rintro n ⟨M, hM, rfl⟩
      apply Finset.card_le_card
      intro e he
      exact Finset.mem_powerset.mpr (H.edges_subset_vertices e (hM.1 e he))
    have hmatch : 1 ≤ H.matchingNumber := by
      apply le_csSup hb
      refine ⟨{e}, ⟨?_, ?_⟩, by simp⟩
      · intro e' he'
        simpa only [Finset.mem_singleton.mp he'] using he
      · intro e₁ he₁ e₂ he₂ hne
        exact (hne ((Finset.mem_singleton.mp he₁).trans (Finset.mem_singleton.mp he₂).symm)).elim
    have hmul : 1 ≤ (r - 1) * H.matchingNumber := by
      exact Nat.mul_le_mul (by omega : 1 ≤ r - 1) hmatch
    exact hcover.trans hmul
  · have hempty : H.edges = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    have hzero : H.coverNumber ≤ 0 := by
      apply Nat.sInf_le
      exact ⟨∅, ⟨Finset.empty_subset _, by simp [hempty]⟩, rfl⟩
    exact hzero.trans (Nat.zero_le _)
