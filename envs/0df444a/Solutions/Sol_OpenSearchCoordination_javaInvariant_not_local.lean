-- Prove2me | solution 1 for OpenSearchCoordination.javaInvariant_not_local
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-01T00:49:59.697774+00:00
-- url     : https://prove2.me/submissions/e20eeb25-9e86-46bd-b077-88f576db4e8a

import Definitions.Def_OpenSearchCoordination

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

/-- ... but not by `handlePublishRequest` in isolation: for the default strategy, a node can satisfy `invariant()`,
accept a publication, and violate it (its join votes become an election quorum of the new configurations without
`electionWon` being set). That `invariant()` nevertheless holds at every cluster-manager-eligible node of every
execution is a property of the cluster: `OpenSearchSafety.javaInvariant_reachable` proves it for that mission's
cluster model, assuming compatible bootstrap configurations and the default strategy. -/
theorem solution :
    ∃ (cs : CoordinationState Unit) (p : PublishRequest Unit) (cs' : CoordinationState Unit) (r : PublishResponse),
      cs.javaInvariant ElectionStrategy.DEFAULT_INSTANCE ∧ cs.handlePublishRequest p = .ok (cs', r) ∧
      ¬ cs'.javaInvariant ElectionStrategy.DEFAULT_INSTANCE := by
  refine ⟨⟨⟨0, true⟩, 1, ⟨0, 0, 0, ⟨[1, 2, 3], by decide⟩, ⟨[1, 2, 3], by decide⟩, none, false, false, ()⟩,
      ⟨[4]⟩, true, false, 0, ⟨[1, 2, 3], by decide⟩, VoteCollection.empty⟩,
    ⟨⟨1, 1, 0, ⟨[4], by decide⟩, ⟨[4], by decide⟩, none, false, false, ()⟩⟩,
    ⟨⟨0, true⟩, 1, ⟨1, 1, 0, ⟨[4], by decide⟩, ⟨[4], by decide⟩, none, false, false, ()⟩,
      ⟨[4]⟩, true, false, 0, ⟨[1, 2, 3], by decide⟩, VoteCollection.empty⟩,
    ⟨1, 1⟩, ?_, ?_, ?_⟩
  · unfold CoordinationState.javaInvariant
    decide
  · rfl
  · unfold CoordinationState.javaInvariant
    decide
