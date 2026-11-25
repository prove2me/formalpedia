-- Prove2me | solution 1 for RandomCNFDeficiency.LowerBound.partial_assignment_of_clause_matching
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-25T20:00:47.943678+00:00
-- url     : https://prove2.me/submissions/6b807af8-98a0-44f8-a0ab-2b5c383aed96

import Definitions.Def_RandomCNFDeficiency_LowerBound_DeficiencyClosure
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
noncomputable section
open RandomCNFDeficiency.LowerBound
open scoped Classical
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BatchCNFPrivate
variable {n : ℕ}
lemma neighbor_union (A B : CNF n) : neighborhood (A ∪ B)=neighborhood A ∪ neighborhood B := by
  ext i
  simp only [neighborhood,Finset.mem_biUnion,Finset.mem_union]
  aesop


lemma gain (T : Finset (Fin n)) (A B : CNF n) :
    deficiency T (A ∪ B)-deficiency T A=
      ((B \ A).card : ℤ)-(((neighborhood B \ T) \ (neighborhood A \ T)).card : ℤ) := by
  have hC := Finset.card_sdiff_add_card B A
  rw [Finset.union_comm B A] at hC
  have hN := Finset.card_sdiff_add_card (neighborhood B \ T) (neighborhood A \ T)
  rw [Finset.union_comm (neighborhood B \ T) (neighborhood A \ T)] at hN
  have he : neighborhood (A ∪ B) \ T=(neighborhood A \ T) ∪ (neighborhood B \ T) := by
    rw [neighbor_union,Finset.union_sdiff_distrib]
  unfold deficiency
  rw [he]
  omega


theorem partial_assignment_of_clause_matching (H : CNF n) (S : Finset (Fin n))
    (m : {C // C ∈ H} → Fin n) (hm : Function.Injective m)
    (hs : ∀ C, m C ∈ clauseSupport C.1 ∧ m C ∉ S) :
    ∃ ρ : Fin n → Option Bool,
      (∀ C ∈ H, PartialSatisfies ρ C) ∧ ∀ i ∈ S, ρ i=none := by
  classical
  let ρ : Fin n → Option Bool := fun i =>
    if h : ∃ C, m C=i then (Classical.choose h).1 i else none
  refine ⟨ρ,?_,?_⟩
  · intro C hC
    let c : {C // C ∈ H} := ⟨C,hC⟩
    have he : ∃ C', m C'=m c := ⟨c,rfl⟩
    have hc : Classical.choose he=c := hm (Classical.choose_spec he)
    have hi := (hs c).1
    have his : (C (m c)).isSome := (Finset.mem_filter.mp hi).2
    cases hv : C (m c) with
    | none => simp [hv] at his
    | some b =>
      refine ⟨m c,b,?_,hv⟩
      dsimp [ρ]
      rw [dif_pos he,hc]
      exact hv
  · intro i hi
    have he : ¬ ∃ C, m C=i := by
      rintro ⟨C,rfl⟩
      exact (hs C).2 hi
    exact dif_neg he


end BatchCNFPrivate
end
open RandomCNFDeficiency.LowerBound

set_option autoImplicit false

theorem solution {n : ℕ} (H : CNF n) (S : Finset (Fin n))
    (m : {C // C ∈ H} → Fin n) (hm : Function.Injective m)
    (hs : ∀ C, m C ∈ clauseSupport C.1 ∧ m C ∉ S) :
    ∃ ρ : Fin n → Option Bool,
      (∀ C ∈ H, PartialSatisfies ρ C) ∧ ∀ i ∈ S, ρ i=none := by
  exact BatchCNFPrivate.partial_assignment_of_clause_matching H S m hm hs