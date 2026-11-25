-- Prove2me | solution 1 for RandomCNFDeficiency.LowerBound.deficiency_supermodular
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-25T17:55:17.088538+00:00
-- url     : https://prove2.me/submissions/46975802-bc58-4c90-94f7-927de153d9a2

import Definitions.Def_RandomCNFDeficiency_LowerBound_DeficiencyClosure
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
noncomputable section
open RandomCNFDeficiency.LowerBound
open scoped Classical
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace RandomCNFSupermodSupport
variable {n : ℕ}

lemma neighbor_mono {A B : CNF n} (h : A ⊆ B) : neighborhood A ⊆ neighborhood B := by
  intro i hi
  obtain ⟨C,hC,hi⟩ := Finset.mem_biUnion.mp hi
  exact Finset.mem_biUnion.mpr ⟨C,h hC,hi⟩

lemma neighbor_union (A B : CNF n) : neighborhood (A ∪ B)=neighborhood A ∪ neighborhood B := by
  ext i
  simp only [neighborhood,Finset.mem_biUnion,Finset.mem_union]
  aesop

lemma neighbor_inter (A B : CNF n) : neighborhood (A ∩ B) ⊆ neighborhood A ∩ neighborhood B := by
  exact Finset.subset_inter (neighbor_mono Finset.inter_subset_left) (neighbor_mono Finset.inter_subset_right)

lemma supermodular (T : Finset (Fin n)) (A B : CNF n) :
    deficiency T A+deficiency T B ≤ deficiency T (A ∪ B)+deficiency T (A ∩ B) := by
  have hC := Finset.card_union_add_card_inter A B
  have hN := Finset.card_union_add_card_inter (neighborhood A \ T) (neighborhood B \ T)
  have hI : (neighborhood (A ∩ B) \ T).card ≤
      ((neighborhood A \ T) ∩ (neighborhood B \ T)).card := by
    apply Finset.card_le_card
    intro i hi
    have hh := Finset.mem_sdiff.mp hi
    have hp := Finset.mem_inter.mp (neighbor_inter A B hh.1)
    simp only [Finset.mem_inter,Finset.mem_sdiff]
    exact ⟨⟨hp.1,hh.2⟩,⟨hp.2,hh.2⟩⟩
  have hU : neighborhood (A ∪ B) \ T=(neighborhood A \ T) ∪ (neighborhood B \ T) := by
    rw [neighbor_union,Finset.union_sdiff_distrib]
  unfold deficiency
  rw [hU]
  omega

end RandomCNFSupermodSupport

end
open RandomCNFDeficiency.LowerBound
open scoped Classical

set_option autoImplicit false

theorem solution {n : ℕ} (T : Finset (Fin n)) (A B : CNF n) :
    deficiency T A + deficiency T B ≤ deficiency T (A ∪ B) + deficiency T (A ∩ B) := by
  exact RandomCNFSupermodSupport.supermodular T A B