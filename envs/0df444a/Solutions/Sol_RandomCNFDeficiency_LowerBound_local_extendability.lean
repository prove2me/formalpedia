-- Prove2me | solution 1 for RandomCNFDeficiency.LowerBound.local_extendability
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-25T20:05:08.074638+00:00
-- url     : https://prove2.me/submissions/5fb7bec6-d121-4aa0-b566-138deae8aaa4

import Theorems.Thm_RandomCNFDeficiency_LowerBound_closure_external_hall
import Theorems.Thm_RandomCNFDeficiency_LowerBound_matching_of_external_hall
import Theorems.Thm_RandomCNFDeficiency_LowerBound_partial_assignment_of_clause_matching
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
namespace BatchCNFPrivate_local_extendability
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


theorem local_extendability (F : CNF n) (s D : ℝ) (hF : Criterion F s D)
    (T : Finset (Fin n)) (hT : (T.card : ℝ) ≤ D)
    (B : CNF n) (hAB : closure F s T ⊆ B) (hBF : B ⊆ F)
    (hB : (B.card : ℝ) ≤ 2*s) :
    ∃ ρ : Fin n → Option Bool,
      (∀ C ∈ B \ closure F s T, PartialSatisfies ρ C) ∧
      ∀ i ∈ T ∪ neighborhood (closure F s T), ρ i=none := by
  obtain ⟨m,hm,hs⟩ := RandomCNFDeficiency.LowerBound.matching_of_external_hall (B \ closure F s T)
    (T ∪ neighborhood (closure F s T)) (RandomCNFDeficiency.LowerBound.closure_external_hall F s D hF T hT B hAB hBF hB)
  exact RandomCNFDeficiency.LowerBound.partial_assignment_of_clause_matching _ _ m hm hs


end BatchCNFPrivate_local_extendability
end
open RandomCNFDeficiency.LowerBound

set_option autoImplicit false



theorem solution
    {n : ℕ} (F : CNF n) (s D : ℝ) (hF : Criterion F s D)
    (T : Finset (Fin n)) (hT : (T.card : ℝ) ≤ D)
    (B : CNF n) (hAB : closure F s T ⊆ B) (hBF : B ⊆ F)
    (hB : (B.card : ℝ) ≤ 2 * s) :
    ∃ ρ : Fin n → Option Bool,
      (∀ C ∈ B \ closure F s T, PartialSatisfies ρ C) ∧
      ∀ i ∈ T ∪ neighborhood (closure F s T), ρ i = none := by
  exact BatchCNFPrivate_local_extendability.local_extendability F s D hF T hT B hAB hBF hB