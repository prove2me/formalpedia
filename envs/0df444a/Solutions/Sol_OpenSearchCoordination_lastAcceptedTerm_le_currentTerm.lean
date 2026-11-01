-- Prove2me | solution 1 for OpenSearchCoordination.lastAcceptedTerm_le_currentTerm
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-01T00:50:22.907197+00:00
-- url     : https://prove2.me/submissions/1b80b20d-9d1b-4164-9541-8e9b78327b6e

import Definitions.Def_OpenSearchCoordination
import Theorems.Thm_OpenSearchCoordination_handleCommit_spec
import Theorems.Thm_OpenSearchCoordination_handlePublishRequest_spec
import Theorems.Thm_OpenSearchCoordination_handleStartJoin_spec

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

/-- At a node whose last accepted term is at most its current term, one successful call of any handler (of
`setInitialState`, with a term-0 state) preserves this inequality; `handleStartJoin` strictly raises the current term,
and every other handler leaves it unchanged. -/
theorem solution {V : Type} (es : ElectionStrategy) (cs : CoordinationState V)
    (hcs : cs.lastAcceptedTerm ≤ cs.currentTerm) :
    (∀ s cs', cs.setInitialState s = .ok cs' → s.term = 0 → cs'.lastAcceptedTerm ≤ cs'.currentTerm ∧
        cs'.currentTerm = cs.currentTerm) ∧
    (∀ r cs' j, cs.handleStartJoin r = .ok (cs', j) → cs'.lastAcceptedTerm ≤ cs'.currentTerm ∧
        cs.currentTerm < cs'.currentTerm) ∧
    (∀ j cs' b, cs.handleJoin es j = .ok (cs', b) → cs'.lastAcceptedTerm ≤ cs'.currentTerm ∧
        cs'.currentTerm = cs.currentTerm) ∧
    (∀ s cs' p, cs.handleClientValue s = .ok (cs', p) → cs'.lastAcceptedTerm ≤ cs'.currentTerm ∧
        cs'.currentTerm = cs.currentTerm) ∧
    (∀ p cs' r, cs.handlePublishRequest p = .ok (cs', r) → cs'.lastAcceptedTerm ≤ cs'.currentTerm ∧
        cs'.currentTerm = cs.currentTerm) ∧
    (∀ n r cs' o, cs.handlePublishResponse n r = .ok (cs', o) → cs'.lastAcceptedTerm ≤ cs'.currentTerm ∧
        cs'.currentTerm = cs.currentTerm) ∧
    (∀ c cs', cs.handleCommit c = .ok cs' → cs'.lastAcceptedTerm ≤ cs'.currentTerm ∧
        cs'.currentTerm = cs.currentTerm) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s cs' h hs
    unfold CoordinationState.setInitialState at h
    split at h
    · cases h
    · simp only [Except.ok.injEq] at h
      subst h
      refine ⟨?_, rfl⟩
      show s.term ≤ cs.currentTerm
      omega
  · intro r cs' j h
    obtain ⟨hlt, h1, h2, -⟩ := (handleStartJoin_spec cs r cs' j).1 h
    unfold CoordinationState.lastAcceptedTerm at hcs ⊢
    rw [h2, h1]
    omega
  · intro j cs' b h
    unfold CoordinationState.handleJoin at h
    split at h
    · cases h
    split at h
    · cases h
    split at h
    · cases h
    split at h
    · cases h
    split at h
    · cases h
    generalize cs.joinVotes.addVote j.sourceNode = va at h
    obtain ⟨votes, added⟩ := va
    dsimp only at h
    split at h
    all_goals
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨hcs, rfl⟩
  · intro s cs' p h
    unfold CoordinationState.handleClientValue at h
    repeat (split at h; · cases h)
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hcs, rfl⟩
  · intro p cs' r h
    obtain ⟨h1, h2, h3, -⟩ := handlePublishRequest_spec cs p cs' r hcs h
    unfold CoordinationState.lastAcceptedTerm
    rw [h1, h3, h2]
    exact ⟨Nat.le_refl _, rfl⟩
  · intro n r cs' o h
    unfold CoordinationState.handlePublishResponse at h
    repeat (split at h; · cases h)
    dsimp only at h
    split at h
    all_goals
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨hcs, rfl⟩
  · intro c cs' h
    obtain ⟨-, -, -, -, -, -, h1, -⟩ := handleCommit_spec cs c cs' h
    obtain ⟨-, -, -, rfl, -⟩ := handleCommit_spec cs c cs' h
    rw [h1]
    exact ⟨hcs, rfl⟩
