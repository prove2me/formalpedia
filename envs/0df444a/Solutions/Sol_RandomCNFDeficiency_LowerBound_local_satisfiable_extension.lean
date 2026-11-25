-- Prove2me | solution 1 for RandomCNFDeficiency.LowerBound.local_satisfiable_extension
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-25T20:06:17.75581+00:00
-- url     : https://prove2.me/submissions/7fd5dc04-f143-4ec4-8640-61ca962b7873

import Theorems.Thm_RandomCNFDeficiency_LowerBound_local_extendability
import Theorems.Thm_RandomCNFDeficiency_LowerBound_satisfying_extension_from_partial
import Theorems.Thm_RandomCNFDeficiency_LowerBound_closure_satisfiable
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
namespace BatchCNFPrivate_local_satisfiable_extension
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


theorem local_satisfiable_extension (F : CNF n) (s D : ℝ) (hF : Criterion F s D)
    (T : Finset (Fin n)) (hT : (T.card : ℝ) ≤ D)
    (B : CNF n) (hAB : closure F s T ⊆ B) (hBF : B ⊆ F)
    (hB : (B.card : ℝ) ≤ 2*s) : Satisfiable B := by
  obtain ⟨ρ,hρ,hn⟩ := RandomCNFDeficiency.LowerBound.local_extendability F s D hF T hT B hAB hBF hB
  exact RandomCNFDeficiency.LowerBound.satisfying_extension_from_partial _ B hAB ρ hρ
    (fun i hi => hn i (Finset.mem_union_right _ hi)) (RandomCNFDeficiency.LowerBound.closure_satisfiable F s D hF T hT)


end BatchCNFPrivate_local_satisfiable_extension
end
open RandomCNFDeficiency.LowerBound

set_option autoImplicit false

theorem solution {n : ℕ} (F : CNF n) (s D : ℝ) (hF : Criterion F s D)
    (T : Finset (Fin n)) (hT : (T.card : ℝ) ≤ D)
    (B : CNF n) (hAB : closure F s T ⊆ B) (hBF : B ⊆ F)
    (hB : (B.card : ℝ) ≤ 2*s) : Satisfiable B := by
  exact BatchCNFPrivate_local_satisfiable_extension.local_satisfiable_extension F s D hF T hT B hAB hBF hB