-- Prove2me | solution 1 for RandomCNFDeficiency.LowerBound.satisfying_extension_from_partial
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-25T20:00:55.308307+00:00
-- url     : https://prove2.me/submissions/afa61e03-6c4f-483d-998f-4a98462994cd

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


theorem satisfying_extension_from_partial (A B : CNF n) (hAB : A ⊆ B)
    (ρ : Fin n → Option Bool) (hρ : ∀ C ∈ B \ A, PartialSatisfies ρ C)
    (hn : ∀ i ∈ neighborhood A, ρ i=none) (ha : Satisfiable A) : Satisfiable B := by
  classical
  obtain ⟨a,ha⟩ := ha
  let b : Assignment n := fun i => (ρ i).getD (a i)
  refine ⟨b,?_⟩
  intro C hC
  by_cases hCA : C ∈ A
  · obtain ⟨i,hi⟩ := ha C hCA
    have hiN : i ∈ neighborhood A := by
      apply Finset.mem_biUnion.mpr
      refine ⟨C,hCA,?_⟩
      simp [clauseSupport,hi]
    refine ⟨i,?_⟩
    simpa [b,hn i hiN] using hi
  · obtain ⟨i,v,hi,hv⟩ := hρ C (Finset.mem_sdiff.mpr ⟨hC,hCA⟩)
    exact ⟨i,by simpa [b,hi] using hv⟩


end BatchCNFPrivate
end
open RandomCNFDeficiency.LowerBound

set_option autoImplicit false

theorem solution {n : ℕ} (A B : CNF n) (hAB : A ⊆ B)
    (ρ : Fin n → Option Bool) (hρ : ∀ C ∈ B \ A, PartialSatisfies ρ C)
    (hn : ∀ i ∈ neighborhood A, ρ i=none) (ha : Satisfiable A) : Satisfiable B := by
  exact BatchCNFPrivate.satisfying_extension_from_partial A B hAB ρ hρ hn ha