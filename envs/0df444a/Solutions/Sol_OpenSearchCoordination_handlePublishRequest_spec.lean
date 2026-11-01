-- Prove2me | solution 1 for OpenSearchCoordination.handlePublishRequest_spec
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-01T00:49:55.77934+00:00
-- url     : https://prove2.me/submissions/e1a750a5-01f1-4c6f-9103-bb27cc477bbe

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

/-- At a node whose last accepted term is at most its current term, `handlePublishRequest` accepts only a state of the
current term, and only one that is strictly newer than the last accepted state in the lexicographic (term, version)
order or has term 0 (the Zen1 compatibility branch, whose condition on the cluster-manager is not stated here). The
response names exactly the accepted state's term and version. -/
theorem solution {V : Type} (cs : CoordinationState V) (req : PublishRequest V) (cs' : CoordinationState V)
    (resp : PublishResponse) (hcs : cs.lastAcceptedTerm ≤ cs.currentTerm)
    (h : cs.handlePublishRequest req = .ok (cs', resp)) :
    cs'.lastAcceptedState = req.acceptedState ∧ req.acceptedState.term = cs.currentTerm ∧
    cs'.currentTerm = cs.currentTerm ∧ cs'.localNode = cs.localNode ∧
    resp = ⟨req.acceptedState.term, req.acceptedState.version⟩ ∧
    (cs.lastAcceptedTerm < req.acceptedState.term ∨
      (cs.lastAcceptedTerm = req.acceptedState.term ∧ cs.lastAcceptedVersion < req.acceptedState.version) ∨
      req.acceptedState.term = ZEN1_BWC_TERM) ∧
    cs'.joinVotes = cs.joinVotes ∧ cs'.electionWon = cs.electionWon ∧
    cs'.startedJoinSinceLastReboot = cs.startedJoinSinceLastReboot ∧
    cs'.lastPublishedVersion = cs.lastPublishedVersion ∧
    cs'.lastPublishedConfiguration = cs.lastPublishedConfiguration ∧ cs'.publishVotes = cs.publishVotes := by
  unfold CoordinationState.handlePublishRequest at h
  dsimp only at h
  split at h
  · cases h
  · rename_i hterm
    have hterm' : req.acceptedState.term = cs.currentTerm := Classical.not_not.mp hterm
    split at h
    · rename_i hle
      split at h
      · rename_i hzen
        split at h
        · cases h
        · split at h
          · simp only [Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact ⟨rfl, hterm', rfl, rfl, rfl, Or.inr (Or.inr hzen), rfl, rfl, rfl, rfl, rfl, rfl⟩
          · cases h
      · cases h
    · rename_i hnle
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨rfl, hterm', rfl, rfl, rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
      by_cases heq : req.acceptedState.term = cs.lastAcceptedTerm
      · right; left
        refine ⟨heq.symm, ?_⟩
        have := fun hv => hnle ⟨heq, hv⟩
        omega
      · left
        unfold CoordinationState.lastAcceptedTerm at heq hcs ⊢
        omega
