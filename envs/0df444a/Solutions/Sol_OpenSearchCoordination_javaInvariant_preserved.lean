-- Prove2me | solution 1 for OpenSearchCoordination.javaInvariant_preserved
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-01T00:50:47.885278+00:00
-- url     : https://prove2.me/submissions/c65c76fd-7625-49ec-9b62-a40aed6311d5

import Definitions.Def_OpenSearchCoordination
import Theorems.Thm_OpenSearchCoordination_handleClientValue_spec
import Theorems.Thm_OpenSearchCoordination_handleJoin_spec
import Theorems.Thm_OpenSearchCoordination_handleJoin_stays_won
import Theorems.Thm_OpenSearchCoordination_handlePublishResponse_spec

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

/-- For a monotone election strategy, `invariant()` is preserved by `handleJoin`, `handleClientValue` and
`handlePublishResponse`. -/
theorem solution {V : Type} (es : ElectionStrategy) (hes : es.Monotone) (cs : CoordinationState V)
    (hinv : cs.javaInvariant es) :
    (∀ j cs' b, cs.handleJoin es j = .ok (cs', b) → cs'.javaInvariant es) ∧
    (∀ s cs' p, cs.handleClientValue s = .ok (cs', p) → cs'.javaInvariant es) ∧
    (∀ n r cs' o, cs.handlePublishResponse n r = .ok (cs', o) → cs'.javaInvariant es) := by
  obtain ⟨i1, i2, i3, i4, i5⟩ := hinv
  refine ⟨?_, ?_, ?_⟩
  · intro j cs' b h
    have hstay := handleJoin_stays_won es hes cs j cs' b i2 h
    obtain ⟨-, hsj, -, -, -, -, he, hct, hlas, hln, hsj', hpv, -, hlpv⟩ := handleJoin_spec es cs j cs' b h
    have hq : cs'.isElectionQuorum es cs'.joinVotes = cs.isElectionQuorum es cs'.joinVotes := by
      unfold CoordinationState.isElectionQuorum CoordinationState.lastCommittedConfiguration
        CoordinationState.lastAcceptedConfiguration CoordinationState.lastAcceptedTerm
        CoordinationState.lastAcceptedVersion
      rw [hct, hlas, hln]
    unfold CoordinationState.javaInvariant
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · unfold CoordinationState.lastAcceptedTerm at i1 ⊢
      rw [hlas, hct]
      exact i1
    · rw [hq]
      exact he
    · have hlav : cs'.lastAcceptedVersion = cs.lastAcceptedVersion := by
        unfold CoordinationState.lastAcceptedVersion
        rw [hlas]
      rw [hlpv, hlav]
      cases hw' : cs'.electionWon <;> cases hw : cs.electionWon <;> simp_all
    · intro _
      rw [hsj']
      exact hsj
    · rw [hpv]
      rcases i5 with i5 | i5
      · exact Or.inl i5
      · exact Or.inr (hstay i5)
  · intro s cs' p h
    obtain ⟨hw, hpv, -, hv, -, -, -, rfl⟩ := handleClientValue_spec cs s cs' p h
    refine ⟨i1, i2, ?_, i4, Or.inl rfl⟩
    show (if cs.electionWon = true then s.version ≥ cs.lastAcceptedVersion else s.version = 0)
    rw [if_pos hw]
    omega
  · intro n r cs' o h
    obtain ⟨hw, -, -, rfl, -⟩ := handlePublishResponse_spec cs n r cs' o h
    exact ⟨i1, i2, i3, i4, Or.inr hw⟩
