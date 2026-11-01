-- Prove2me | solution 1 for OpenSearchCoordination.handleCommit_spec
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-01T00:49:56.396202+00:00
-- url     : https://prove2.me/submissions/978be0d1-1a61-4b13-84dd-51a247175235

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

/-- `handleCommit` changes nothing but the last accepted state's committed configuration (which becomes the accepted
one, the assertion of CS:572) and its cluster-UUID flag; it applies only to the last accepted state, and only in the
current term. -/
theorem solution {V : Type} (cs : CoordinationState V) (c : ApplyCommitRequest) (cs' : CoordinationState V)
    (h : cs.handleCommit c = .ok cs') :
    c.term = cs.currentTerm ∧ c.term = cs.lastAcceptedTerm ∧ c.version = cs.lastAcceptedVersion ∧
    cs' = { cs with lastAcceptedState := cs.lastAcceptedState.markCommitted } ∧
    cs'.lastCommittedConfiguration = cs'.lastAcceptedConfiguration ∧
    cs'.lastAcceptedConfiguration = cs.lastAcceptedConfiguration ∧
    cs'.lastAcceptedTerm = cs.lastAcceptedTerm ∧ cs'.lastAcceptedVersion = cs.lastAcceptedVersion ∧
    cs'.lastAcceptedState.value = cs.lastAcceptedState.value := by
  unfold CoordinationState.handleCommit at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · rename_i h1 h2 h3
        simp only [Except.ok.injEq] at h
        subst h
        refine ⟨Classical.not_not.mp h1, Classical.not_not.mp h2, Classical.not_not.mp h3, rfl, ?_, ?_, ?_, ?_, ?_⟩
        all_goals
          simp only [CoordinationState.lastCommittedConfiguration, CoordinationState.lastAcceptedConfiguration,
            CoordinationState.lastAcceptedTerm, CoordinationState.lastAcceptedVersion, ClusterState.markCommitted]
          split <;> split <;> simp_all
