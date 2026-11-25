-- Prove2me | solution 1 for RandomCNFDeficiency.LowerBound.closure_contains_supported_clause
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-25T20:02:19.109037+00:00
-- url     : https://prove2.me/submissions/366ba91a-2be7-4f1c-8c47-81bc077dd16a

import Theorems.Thm_RandomCNFDeficiency_LowerBound_closure_largest_maximizer
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


theorem closure_contains_supported_clause (F : CNF n) (s D : ℝ) (hF : Criterion F s D)
    (T : Finset (Fin n)) (hT : (T.card : ℝ) ≤ D)
    (C : Clause n) (hCF : C ∈ F) (hCT : clauseSupport C ⊆ T) : C ∈ closure F s T := by
  classical
  let A := closure F s T
  have hA := RandomCNFDeficiency.LowerBound.closure_largest_maximizer F s D hF T hT
  by_contra hC
  have hcard : ((insert C A).card : ℝ) ≤ 2*s := by
    rw [Finset.card_insert_of_notMem hC,Nat.cast_add,Nat.cast_one]
    have hh : (A.card : ℝ) < s := hA.2.1
    linarith [hF.1]
  have hN : neighborhood (insert C A) \ T=neighborhood A \ T := by
    have hnn : neighborhood (insert C A)=clauseSupport C ∪ neighborhood A := by
      simp only [neighborhood,Finset.biUnion_insert]
    rw [hnn,Finset.union_sdiff_distrib,Finset.sdiff_eq_empty_iff_subset.mpr hCT,Finset.empty_union]
  have hmax := hA.1.2 (insert C A) ⟨Finset.insert_subset hCF hA.1.1.1,hcard⟩
  unfold deficiency at hmax
  rw [hN,Finset.card_insert_of_notMem hC] at hmax
  dsimp only [A] at hmax
  omega

end BatchCNFPrivate
end
open RandomCNFDeficiency.LowerBound

set_option autoImplicit false

theorem solution {n : ℕ} (F : CNF n) (s D : ℝ) (hF : Criterion F s D)
    (T : Finset (Fin n)) (hT : (T.card : ℝ) ≤ D)
    (C : Clause n) (hCF : C ∈ F) (hCT : clauseSupport C ⊆ T) : C ∈ closure F s T := by
  exact BatchCNFPrivate.closure_contains_supported_clause F s D hF T hT C hCF hCT