-- Prove2me | solution 1 for RandomCNFDeficiency.LowerBound.closure_external_hall
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-25T20:03:44.93405+00:00
-- url     : https://prove2.me/submissions/29bf7b52-84d4-4236-85de-b0c3d3b3f5db

import Theorems.Thm_RandomCNFDeficiency_LowerBound_deficiency_union_increment
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
namespace BatchCNFPrivate_closure_external_hall
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


theorem closure_external_hall (F : CNF n) (s D : ℝ) (hF : Criterion F s D)
    (T : Finset (Fin n)) (hT : (T.card : ℝ) ≤ D)
    (B : CNF n) (hAB : closure F s T ⊆ B) (hBF : B ⊆ F)
    (hB : (B.card : ℝ) ≤ 2*s) :
    ∀ L ⊆ B \ closure F s T,
      L.card ≤ (neighborhood L \ (T ∪ neighborhood (closure F s T))).card := by
  intro L hL
  have hA := RandomCNFDeficiency.LowerBound.closure_largest_maximizer F s D hF T hT
  have hLB : L ⊆ B := Finset.Subset.trans hL Finset.sdiff_subset
  have hu : closure F s T ∪ L ⊆ B := Finset.union_subset hAB hLB
  have had : Admissible F s (closure F s T ∪ L) := by
    refine ⟨Finset.Subset.trans hu hBF,?_⟩
    have hc : ((closure F s T ∪ L).card : ℝ) ≤ B.card := by
      exact_mod_cast Finset.card_le_card hu
    linarith
  have hm := hA.1.2 _ had
  have hd : Disjoint (closure F s T) L := by
    apply Finset.disjoint_left.mpr
    intro C hC hCL
    exact (Finset.mem_sdiff.mp (hL hCL)).2 hC
  rw [← sub_nonpos,RandomCNFDeficiency.LowerBound.deficiency_union_increment T _ L hd] at hm
  omega


end BatchCNFPrivate_closure_external_hall
end
open RandomCNFDeficiency.LowerBound

set_option autoImplicit false

theorem solution {n : ℕ} (F : CNF n) (s D : ℝ) (hF : Criterion F s D)
    (T : Finset (Fin n)) (hT : (T.card : ℝ) ≤ D)
    (B : CNF n) (hAB : closure F s T ⊆ B) (hBF : B ⊆ F)
    (hB : (B.card : ℝ) ≤ 2*s) :
    ∀ L ⊆ B \ closure F s T,
      L.card ≤ (neighborhood L \ (T ∪ neighborhood (closure F s T))).card := by
  exact BatchCNFPrivate_closure_external_hall.closure_external_hall F s D hF T hT B hAB hBF hB