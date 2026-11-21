-- Prove2me | solution 1 for ReconfRes.Frozen.proposition_3_3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T12:44:00.051869+00:00
-- url     : https://prove2.me/submissions/feed9423-d55c-4f80-a597-d51dc1f21a55

import Mathlib
import Definitions.Def_MultiplierAssoc206_Resolution_CNF
import Definitions.Def_ReconfRes_Frozen_Refutation
import Definitions.Def_ReconfRes_Frozen_FrozenGraph

section
open MultiplierAssoc206.Resolution
namespace ReconfRes.Frozen
namespace Dev.P33
variable {V : Type} [DecidableEq V]

theorem mem_parents (R : ProofDag V) (i j : Fin R.n) : j ∈ R.parents i ↔ (j, i) ∈ R.edges := by
  simp [ProofDag.parents]

theorem mem_consumers (R : ProofDag V) (i j : Fin R.n) : j ∈ R.consumers i ↔ (i, j) ∈ R.edges := by
  simp [ProofDag.consumers]

theorem hasParent_iff {k : ℕ} {R R' : ProofDag V} {Q : Finset (Fin R.n)} {Q' : Finset (Fin R'.n)}
    {φ : {i // i ∉ Q} ≃ {j // j ∉ Q'}} (h : MoveVia k R R' Q Q' φ) (a : {i // i ∉ Q}) :
    R.parents a.1 = ∅ ↔ R'.parents (φ a).1 = ∅ := by
  obtain ⟨q, q', ⟨_, _, hbq⟩, ⟨_, _, hbq'⟩, _, _, hed, _, hcons, _, _⟩ := h
  constructor
  · intro hp
    rw [Finset.eq_empty_iff_forall_notMem] at hp ⊢
    intro j hj
    rw [mem_parents] at hj
    by_cases hjQ : j ∈ Q'
    · by_cases hjq : j = q'
      · subst hjq
        have := (hcons a).1 hj
        exact hp q ((mem_parents R _ _).2 this)
      · have := hbq' j hjQ hjq
        have hm : (φ a).1 ∈ R'.consumers j := (mem_consumers R' _ _).2 hj
        exact (φ a).2 (this hm)
    · obtain ⟨p, hp'⟩ := φ.surjective ⟨j, hjQ⟩
      have : (j, (φ a).1) ∈ R'.edges := hj
      have hp'' : (φ p).1 = j := by rw [hp']
      rw [← hp''] at this
      have := (hed p a).1 this
      exact hp p.1 ((mem_parents R _ _).2 this)
  · intro hp
    rw [Finset.eq_empty_iff_forall_notMem] at hp ⊢
    intro j hj
    rw [mem_parents] at hj
    by_cases hjQ : j ∈ Q
    · by_cases hjq : j = q
      · subst hjq
        exact hp q' ((mem_parents R' _ _).2 ((hcons a).2 hj))
      · have := hbq j hjQ hjq
        have hm : a.1 ∈ R.consumers j := (mem_consumers R _ _).2 hj
        exact a.2 (this hm)
    · exact hp (φ ⟨j, hjQ⟩).1 ((mem_parents R' _ _).2 ((hed ⟨j, hjQ⟩ a).2 hj))

theorem axiomMultiset_eq_of_move {k : ℕ} {R R' : ProofDag V} {Q : Finset (Fin R.n)}
    {Q' : Finset (Fin R'.n)} {φ : {i // i ∉ Q} ≃ {j // j ∉ Q'}}
    (h : FrozenMoveVia k R R' Q Q' φ) : R.axiomMultiset = R'.axiomMultiset := by
  obtain ⟨hm, hQ, hQ'⟩ := h
  have hlab := hm
  obtain ⟨q, q', _, _, _, hl, _⟩ := hlab
  unfold ProofDag.axiomMultiset
  have hnQ : ∀ a, R.parents a = ∅ → a ∉ Q := fun a ha haQ => hQ a haQ ha
  refine Multiset.map_eq_map_of_bij_of_nodup R.label R'.label (Finset.nodup _) (Finset.nodup _)
    (fun a ha => (φ ⟨a, hnQ a (by simpa using ha)⟩).1) ?_ ?_ ?_ ?_
  · intro a ha
    have ha' : R.parents a = ∅ := by simpa using ha
    simpa using (hasParent_iff hm ⟨a, hnQ a ha'⟩).1 ha'
  · intro a b ha hb hab
    have := φ.injective (Subtype.ext hab)
    simpa using this
  · intro b hb
    have hb' : R'.parents b = ∅ := by simpa using hb
    have hbQ' : b ∉ Q' := fun h => hQ' b h hb'
    obtain ⟨a, ha⟩ := φ.surjective ⟨b, hbQ'⟩
    have hpa : R.parents a.1 = ∅ := (hasParent_iff hm a).2 (by rw [ha]; exact hb')
    refine ⟨a.1, by simpa using hpa, ?_⟩
    simp [ha]
  · intro a ha
    exact (hl ⟨a, hnQ a (by simpa using ha)⟩).symm

theorem axiomMultiset_eq_of_iso {R R' : ProofDag V} (h : R.Iso R') :
    R.axiomMultiset = R'.axiomMultiset := by
  obtain ⟨e, hl, he, _⟩ := h
  unfold ProofDag.axiomMultiset
  have key : ∀ a, R.parents a = ∅ ↔ R'.parents (e a) = ∅ := by
    intro a
    constructor
    · intro hp
      rw [Finset.eq_empty_iff_forall_notMem] at hp ⊢
      intro j hj
      rw [mem_parents] at hj
      obtain ⟨j', rfl⟩ := e.surjective j
      exact hp j' ((mem_parents R _ _).2 ((he j' a).1 hj))
    · intro hp
      rw [Finset.eq_empty_iff_forall_notMem] at hp ⊢
      intro j hj
      rw [mem_parents] at hj
      exact hp (e j) ((mem_parents R' _ _).2 ((he j a).2 hj))
  refine Multiset.map_eq_map_of_bij_of_nodup R.label R'.label (Finset.nodup _) (Finset.nodup _)
    (fun a _ => e a) ?_ ?_ ?_ ?_
  · intro a ha; simpa [key] using ha
  · intro a b _ _ hab; exact e.injective hab
  · intro b hb
    obtain ⟨a, rfl⟩ := e.surjective b
    exact ⟨a, by simpa [key] using hb, rfl⟩
  · intro a _; exact (hl a).symm

theorem axiomMultiset_eq_of_move' {k : ℕ} {R R' : ProofDag V} (h : FrozenMove k R R') :
    R.axiomMultiset = R'.axiomMultiset := by
  obtain ⟨Q, Q', φ, h⟩ := h
  exact axiomMultiset_eq_of_move h

theorem step_eq {k : ℕ} {F : CNF V} {w s : ℕ} {R R' : ProofDag V} (h : FrozenStep k F w s R R') :
    R.axiomMultiset = R'.axiomMultiset := by
  obtain ⟨_, _, h | h | h⟩ := h
  · exact axiomMultiset_eq_of_iso h
  · exact axiomMultiset_eq_of_move' h
  · exact (axiomMultiset_eq_of_move' h).symm

theorem conn_eq {k : ℕ} {F : CNF V} {w s : ℕ} {R R' : ProofDag V}
    (hc : FrozenConnected k F w s R R') : R.axiomMultiset = R'.axiomMultiset := by
  induction hc with
  | refl => rfl
  | tail _ hs ih => exact ih.trans (step_eq hs)

theorem main (k : ℕ) (hk : 1 ≤ k) (F : CNF V) (w s : ℕ) :
    (∀ R R' : ProofDag V, FrozenAdj k F w s R R' → R.axiomMultiset = R'.axiomMultiset) ∧
    (∀ R R' : ProofDag V, IsVertex F w s R → IsVertex F w s R' →
      R.axiomMultiset ≠ R'.axiomMultiset → ¬ FrozenConnected k F w s R R') := by
  refine ⟨?_, ?_⟩
  · rintro R R' ⟨_, _, h | h⟩
    · exact axiomMultiset_eq_of_move' h
    · exact (axiomMultiset_eq_of_move' h).symm
  · intro R R' _ _ hne hc
    exact hne (conn_eq hc)
end Dev.P33

theorem chk_proposition_3_3 {V : Type} [DecidableEq V] (k : ℕ) (hk : 1 ≤ k) (F : CNF V) (w s : ℕ) :
    (∀ R R' : ProofDag V, FrozenAdj k F w s R R' → R.axiomMultiset = R'.axiomMultiset) ∧
    (∀ R R' : ProofDag V, IsVertex F w s R → IsVertex F w s R' →
      R.axiomMultiset ≠ R'.axiomMultiset → ¬ FrozenConnected k F w s R R') :=
  Dev.P33.main k hk F w s
end ReconfRes.Frozen
end

theorem solution : type_of% @ReconfRes.Frozen.chk_proposition_3_3 := @ReconfRes.Frozen.chk_proposition_3_3
