-- Prove2me | solution 1 for OpenSearchCoordination.handleStartJoin_spec
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-01T00:49:55.137399+00:00
-- url     : https://prove2.me/submissions/9c086390-3e8e-4bf1-b9a5-ef73ae243173

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

/-- `handleStartJoin` succeeds exactly when the requested term is greater than the current term; it moves the node to
that term, discards the election and publication state, and votes for the requester with the node's last accepted
term and version (or metadata version, for a term-0 state). The accepted state is unchanged. -/
theorem solution {V : Type} (cs : CoordinationState V) (req : StartJoinRequest) (cs' : CoordinationState V)
    (j : Join) :
    cs.handleStartJoin req = .ok (cs', j) ↔
      cs.currentTerm < req.term ∧ cs'.currentTerm = req.term ∧ cs'.lastAcceptedState = cs.lastAcceptedState ∧
      cs'.localNode = cs.localNode ∧ cs'.startedJoinSinceLastReboot = true ∧ cs'.electionWon = false ∧
      cs'.joinVotes = VoteCollection.empty ∧ cs'.publishVotes = VoteCollection.empty ∧
      cs'.lastPublishedVersion = 0 ∧ cs'.lastPublishedConfiguration = cs.lastAcceptedConfiguration ∧
      j = ⟨cs.localNode, req.sourceNode, req.term, cs.lastAcceptedTerm, cs.lastAcceptedVersionOrMetadataVersion⟩ := by
  unfold CoordinationState.handleStartJoin
  constructor
  · intro h
    split at h
    · cases h
    · rename_i hlt
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨by omega, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · rintro ⟨hlt, h1, h2, h3, h4, h5, h6, h7, h8, h9, rfl⟩
    rw [if_neg (show ¬ (req.term ≤ cs.currentTerm) by omega)]
    obtain ⟨ln, ct, las, jv, sj, ew, lpv, lpc, pv⟩ := cs'
    dsimp only at h1 h2 h3 h4 h5 h6 h7 h8 h9
    subst h1 h2 h3 h4 h5 h6 h7 h8 h9
    rfl
