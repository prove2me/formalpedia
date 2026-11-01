-- Prove2me | solution 1 for OpenSearchCoordination.handleJoin_stays_won
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-01T00:50:23.844179+00:00
-- url     : https://prove2.me/submissions/546191bc-5235-41fb-9f72-a52384e5fa7e

import Definitions.Def_OpenSearchCoordination
import Theorems.Thm_OpenSearchCoordination_addVote_eligible
import Theorems.Thm_OpenSearchCoordination_handleJoin_spec
import Theorems.Thm_OpenSearchCoordination_quorum_mono

open OpenSearchCoordination

/-- Counting: an element satisfying both `p` and `q` is counted at most twice on the left and once on each side. -/
private theorem filter_length_add_le {α : Type} (L : List α) (p q : α → Bool) :
    (L.filter p).length + (L.filter q).length ≤ L.length + (L.filter (fun x => p x && q x)).length := by
  induction L with
  | nil => simp
  | cons y ys ih =>
    cases hp : p y <;> cases hq : q y <;> simp [hp, hq] <;> omega

/-- Filtering by a weaker predicate keeps at least as many elements. -/
private theorem filter_length_mono {α : Type} (L : List α) (p q : α → Bool)
    (h : ∀ x, p x = true → q x = true) :
    (L.filter p).length ≤ (L.filter q).length := by
  induction L with
  | nil => simp
  | cons y ys ih =>
    cases hp : p y <;> cases hq : q y <;> simp [hp, hq] <;> try omega
    have := h y hp
    rw [hq] at this
    exact absurd this (by decide)

/-- "We cannot go from won to not won" (the assertion of CS:323-324): for a monotone election strategy, if `electionWon`
agrees with the election quorum before a join (the second clause of `invariant()`), a won election stays won. -/
theorem solution {V : Type} (es : ElectionStrategy) (hes : es.Monotone) (cs : CoordinationState V) (j : Join)
    (cs' : CoordinationState V) (b : Bool) (hinv : cs.electionWon = cs.isElectionQuorum es cs.joinVotes)
    (h : cs.handleJoin es j = .ok (cs', b)) (hw : cs.electionWon = true) : cs'.electionWon = true := by
  obtain ⟨-, -, -, -, hj, -, he, -⟩ := handleJoin_spec es cs j cs' b h
  have hsub : ∀ x, x ∈ cs.joinVotes.nodes → x ∈ cs'.joinVotes.nodes := by
    intro x hx
    rw [hj, addVote_eligible]
    exact Or.inl hx
  rw [hw] at hinv
  have hq := hinv.symm
  unfold CoordinationState.isElectionQuorum VoteCollection.isQuorum at hq
  rw [he]
  unfold CoordinationState.isElectionQuorum VoteCollection.isQuorum
  simp only [Bool.and_eq_true] at hq ⊢
  obtain ⟨⟨hc, ha⟩, hs⟩ := hq
  exact ⟨⟨quorum_mono _ _ _ hsub hc, quorum_mono _ _ _ hsub ha⟩, hes _ _ _ _ _ _ _ _ hsub hs⟩
