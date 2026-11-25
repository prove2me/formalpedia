-- Prove2me | solution 1 for RandomCNFDeficiency.LowerBound.matching_of_external_hall
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-25T20:00:41.590287+00:00
-- url     : https://prove2.me/submissions/5e8ab976-448f-41b4-99f1-b4ca150f1f3d

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


theorem matching_of_external_hall (H : CNF n) (S : Finset (Fin n))
    (hH : ∀ L ⊆ H, L.card ≤ (neighborhood L \ S).card) :
    ∃ m : {C // C ∈ H} → Fin n, Function.Injective m ∧
      ∀ C, m C ∈ clauseSupport C.1 ∧ m C ∉ S := by
  classical
  let t : {C // C ∈ H} → Finset (Fin n) := fun C => clauseSupport C.1 \ S
  have ht : ∀ I : Finset {C // C ∈ H}, I.card ≤ (I.biUnion t).card := by
    intro I
    let L := I.image Subtype.val
    have hL : L ⊆ H := by
      intro C hC
      obtain ⟨C,hC,rfl⟩ := Finset.mem_image.mp hC
      exact C.2
    have hc : L.card=I.card := Finset.card_image_of_injective I Subtype.val_injective
    have he : I.biUnion t=neighborhood L \ S := by
      ext i
      simp only [t,neighborhood,L,Finset.mem_biUnion,Finset.mem_sdiff,Finset.mem_image]
      constructor
      · rintro ⟨C,hC,hi,hs⟩
        exact ⟨⟨C.1,⟨C,hC,rfl⟩,hi⟩,hs⟩
      · rintro ⟨⟨C,⟨C',hC',rfl⟩,hi⟩,hs⟩
        exact ⟨C',hC',hi,hs⟩
    rw [he,← hc]
    exact hH L hL
  obtain ⟨m,hm,htm⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' t).mp ht
  exact ⟨m,hm,fun C => Finset.mem_sdiff.mp (htm C)⟩


end BatchCNFPrivate
end
open RandomCNFDeficiency.LowerBound

set_option autoImplicit false

theorem solution {n : ℕ} (H : CNF n) (S : Finset (Fin n))
    (hH : ∀ L ⊆ H, L.card ≤ (neighborhood L \ S).card) :
    ∃ m : {C // C ∈ H} → Fin n, Function.Injective m ∧
      ∀ C, m C ∈ clauseSupport C.1 ∧ m C ∉ S := by
  exact BatchCNFPrivate.matching_of_external_hall H S hH