-- Prove2me | solution 1 for RandomCNFDeficiency.LowerBound.closure_monotonicity
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-25T18:03:25.008491+00:00
-- url     : https://prove2.me/submissions/6cc0ee03-ba97-46bb-8223-0a6a10c0cb0c

import Theorems.Thm_RandomCNFDeficiency_LowerBound_deficiency_supermodular
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
namespace RandomCNFClosure20
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

lemma exists_max (F : CNF n) (s : ℝ) (hs : 0 ≤ s) (T : Finset (Fin n)) :
    ∃ A, MaximizesDeficiency F s T A := by
  let S := F.powerset.filter (fun A => (A.card : ℝ) ≤ 2*s)
  have hS : S.Nonempty := by
    refine ⟨∅,?_⟩
    simp only [S,Finset.mem_filter,Finset.mem_powerset,Finset.empty_subset,Finset.card_empty,Nat.cast_zero,true_and]
    linarith
  obtain ⟨A,hA,hm⟩ := Finset.exists_max_image S (deficiency T) hS
  have hAA : Admissible F s A := by
    simpa only [S,Finset.mem_filter,Finset.mem_powerset,Admissible] using hA
  refine ⟨A,hAA,?_⟩
  intro B hB
  exact hm B (by simpa only [S,Finset.mem_filter,Finset.mem_powerset,Admissible] using hB)

lemma max_small (F : CNF n) (s D : ℝ) (hF : Criterion F s D)
    (T : Finset (Fin n)) (hT : (T.card : ℝ) ≤ D) (A : CNF n)
    (hA : MaximizesDeficiency F s T A) : (A.card : ℝ) < s := by
  have he : Admissible F s (∅ : CNF n) := by
    refine ⟨Finset.empty_subset _,?_⟩
    simp only [Finset.card_empty,Nat.cast_zero]
    linarith [hF.1]
  have hnon := hA.2 ∅ he
  have h0 : deficiency T (∅ : CNF n)=0 := by simp [deficiency,neighborhood]
  rw [h0] at hnon
  have hcard : (neighborhood A \ T).card ≤ A.card := by
    unfold deficiency at hnon
    omega
  have hi := Finset.card_le_card (Finset.inter_subset_right : neighborhood A ∩ T ⊆ T)
  have heq := Finset.card_sdiff_add_card_inter (neighborhood A) T
  have hbound : ((neighborhood A).card : ℝ) ≤ (A.card : ℝ)+T.card := by
    have hh : (neighborhood A).card ≤ A.card+T.card := by omega
    exact_mod_cast hh
  by_contra h
  have hx := hF.2.2.2.2.2 A hA.1.1 (le_of_not_gt h) hA.1.2
  linarith

lemma union_max (F : CNF n) (s D : ℝ) (hF : Criterion F s D)
    (T : Finset (Fin n)) (hT : (T.card : ℝ) ≤ D) (A B : CNF n)
    (hA : MaximizesDeficiency F s T A) (hB : MaximizesDeficiency F s T B) :
    MaximizesDeficiency F s T (A ∪ B) := by
  have hAs := max_small F s D hF T hT A hA
  have hBs := max_small F s D hF T hT B hB
  have hUc : ((A ∪ B).card : ℝ) ≤ 2*s := by
    have hh : ((A ∪ B).card : ℝ) ≤ (A.card : ℝ)+B.card := by exact_mod_cast Finset.card_union_le A B
    linarith
  have hU : Admissible F s (A ∪ B) := ⟨Finset.union_subset hA.1.1 hB.1.1,hUc⟩
  have hI : Admissible F s (A ∩ B) := by
    refine ⟨Finset.Subset.trans Finset.inter_subset_left hA.1.1,?_⟩
    have hh : ((A ∩ B).card : ℝ) ≤ (A.card : ℝ) := by exact_mod_cast Finset.card_le_card (Finset.inter_subset_left : A ∩ B ⊆ A)
    linarith [hA.1.2]
  have hs := RandomCNFDeficiency.LowerBound.deficiency_supermodular T A B
  have hi := hA.2 _ hI
  have hab := hA.2 B hB.1
  have hba := hB.2 A hA.1
  refine ⟨hU,?_⟩
  intro C hC
  have hh := hA.2 C hC
  linarith

lemma largest (F : CNF n) (s D : ℝ) (hF : Criterion F s D)
    (T : Finset (Fin n)) (hT : (T.card : ℝ) ≤ D) :
    MaximizesDeficiency F s T (closure F s T) ∧
    ((closure F s T).card : ℝ) < s ∧
    (∀ A, MaximizesDeficiency F s T A → A ⊆ closure F s T) ∧
    (∃! A : CNF n, MaximizesDeficiency F s T A ∧
      ∀ B, MaximizesDeficiency F s T B → B ⊆ A) := by
  let S := F.powerset.filter (fun A => MaximizesDeficiency F s T A)
  have hmem (A : CNF n) : A ∈ S ↔ MaximizesDeficiency F s T A := by
    simp only [S,Finset.mem_filter,Finset.mem_powerset]
    exact ⟨And.right,fun h => ⟨h.1.1,h⟩⟩
  obtain ⟨A0,hA0⟩ := exists_max F s (by linarith [hF.1]) T
  have hS : S.Nonempty := ⟨A0,(hmem A0).mpr hA0⟩
  obtain ⟨A,hAS,hmax⟩ := Finset.exists_max_image S Finset.card hS
  have hA := (hmem A).mp hAS
  have hlarge : ∀ B, MaximizesDeficiency F s T B → B ⊆ A := by
    intro B hB
    have hU := union_max F s D hF T hT A B hA hB
    have hc := hmax (A ∪ B) ((hmem _).mpr hU)
    have he : A=A ∪ B := Finset.eq_of_subset_of_card_le Finset.subset_union_left hc
    rw [he]
    exact Finset.subset_union_right
  have he : closure F s T=A := by
    change S.biUnion id=A
    apply Finset.Subset.antisymm
    · intro C hC
      obtain ⟨B,hBS,hCB⟩ := Finset.mem_biUnion.mp hC
      exact hlarge B ((hmem B).mp hBS) hCB
    · intro C hC
      exact Finset.mem_biUnion.mpr ⟨A,hAS,hC⟩
  rw [he]
  refine ⟨hA,max_small F s D hF T hT A hA,hlarge,⟨A,⟨hA,hlarge⟩,?_⟩⟩
  intro B hB
  exact Finset.Subset.antisymm (hlarge B hB.1) (hB.2 A hA)
lemma conditioning_diff (T T' : Finset (Fin n)) (hTT' : T ⊆ T') (A : CNF n) :
    deficiency T' A-deficiency T A=((neighborhood A ∩ (T' \ T)).card : ℤ) := by
  have h1 : (neighborhood A \ T) \ (T' \ T)=neighborhood A \ T' := by
    ext i
    simp only [Finset.mem_sdiff]
    constructor
    · rintro ⟨⟨hN,hT⟩,hT'⟩
      exact ⟨hN,fun h => hT' ⟨h,hT⟩⟩
    · rintro ⟨hN,hT'⟩
      exact ⟨⟨hN,fun h => hT' (hTT' h)⟩,fun h => hT' h.1⟩
  have h2 : (neighborhood A \ T) ∩ (T' \ T)=neighborhood A ∩ (T' \ T) := by
    ext i
    simp only [Finset.mem_sdiff,Finset.mem_inter]
    aesop
  have hc := Finset.card_sdiff_add_card_inter (neighborhood A \ T) (T' \ T)
  rw [h1,h2] at hc
  unfold deficiency
  omega

lemma conditioning_mono (T T' : Finset (Fin n)) (hTT' : T ⊆ T')
    (A B : CNF n) (hAB : A ⊆ B) :
    deficiency T' A-deficiency T A ≤ deficiency T' B-deficiency T B := by
  rw [conditioning_diff T T' hTT',conditioning_diff T T' hTT']
  have h := Finset.card_le_card (Finset.inter_subset_inter (neighbor_mono hAB)
    (Finset.Subset.refl (T' \ T)))
  exact_mod_cast h

lemma union_admissible (F : CNF n) (s : ℝ) (A B : CNF n)
    (hA : A ⊆ F) (hB : B ⊆ F) (hAs : (A.card : ℝ) < s) (hBs : (B.card : ℝ) < s) :
    Admissible F s (A ∪ B) := by
  refine ⟨Finset.union_subset hA hB,?_⟩
  have h : ((A ∪ B).card : ℝ) ≤ (A.card : ℝ)+B.card := by exact_mod_cast Finset.card_union_le A B
  linarith

lemma monotonicity (F : CNF n) (s D : ℝ) (hF : Criterion F s D)
    (T T' : Finset (Fin n)) (hTT' : T ⊆ T') (hT' : (T'.card : ℝ) ≤ D) :
    closure F s T ⊆ closure F s T' := by
  have hT : (T.card : ℝ) ≤ D := by
    have h : (T.card : ℝ) ≤ T'.card := by exact_mod_cast Finset.card_le_card hTT'
    linarith
  let A := closure F s T
  let B := closure F s T'
  have hA := largest F s D hF T hT
  have hB := largest F s D hF T' hT'
  have hU : Admissible F s (A ∪ B) := union_admissible F s A B hA.1.1.1 hB.1.1.1 hA.2.1 hB.2.1
  have hI : Admissible F s (A ∩ B) := by
    refine ⟨Finset.Subset.trans Finset.inter_subset_left hA.1.1.1,?_⟩
    have h : ((A ∩ B).card : ℝ) ≤ (A.card : ℝ) := by
      exact_mod_cast Finset.card_le_card (Finset.inter_subset_left : A ∩ B ⊆ A)
    linarith [hA.1.1.2]
  have hs := RandomCNFDeficiency.LowerBound.deficiency_supermodular T A B
  have hi := hA.1.2 (A ∩ B) hI
  have hd := conditioning_mono T T' hTT' B (A ∪ B) Finset.subset_union_right
  have hnew : MaximizesDeficiency F s T' (A ∪ B) := by
    refine ⟨hU,?_⟩
    intro C hC
    have hc := hB.1.2 C hC
    linarith
  have hinc := hB.2.2.1 (A ∪ B) hnew
  exact Finset.Subset.trans Finset.subset_union_left hinc

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

lemma absorption (F : CNF n) (s D : ℝ) (hF : Criterion F s D)
    (T : Finset (Fin n)) (hT : (T.card : ℝ) ≤ D)
    (U : Finset (Fin n)) (hU : (U.card : ℝ) ≤ D)
    (hUT : U ⊆ T ∪ neighborhood (closure F s T)) :
    closure F s U ⊆ closure F s T := by
  let A := closure F s T
  let B := closure F s U
  have hA := largest F s D hF T hT
  have hB := largest F s D hF U hU
  have hAB : Admissible F s (A ∪ B) := union_admissible F s A B hA.1.1.1 hB.1.1.1 hA.2.1 hB.2.1
  have hI : Admissible F s (A ∩ B) := by
    refine ⟨Finset.Subset.trans Finset.inter_subset_right hB.1.1.1,?_⟩
    have h : ((A ∩ B).card : ℝ) ≤ (B.card : ℝ) := by
      exact_mod_cast Finset.card_le_card (Finset.inter_subset_right : A ∩ B ⊆ B)
    linarith [hB.1.1.2]
  have hNI : neighborhood (A ∩ B) \ U ⊆ neighborhood B \ U :=
    Finset.sdiff_subset_sdiff (neighbor_mono Finset.inter_subset_right) (Finset.Subset.refl U)
  have hNew : (neighborhood B \ T) \ (neighborhood A \ T) ⊆
      (neighborhood B \ U) \ (neighborhood (A ∩ B) \ U) := by
    intro i hi
    have hb : i ∈ neighborhood B := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hi).1).1
    have ht : i ∉ T := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hi).1).2
    have ha : i ∉ neighborhood A := by
      intro ha
      exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_sdiff.mpr ⟨ha,ht⟩)
    have hu : i ∉ U := by
      intro hu
      rcases Finset.mem_union.mp (hUT hu) with h|h
      · exact ht h
      · exact ha h
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨hb,hu⟩,?_⟩
    intro h
    exact ha (neighbor_mono Finset.inter_subset_left (Finset.mem_sdiff.mp h).1)
  have hcard := Finset.card_le_card hNew
  have hcN := Finset.card_sdiff_add_card_eq_card hNI
  have hcB := Finset.card_sdiff_add_card_inter B A
  rw [Finset.inter_comm B A] at hcB
  have hmax := hB.1.2 (A ∩ B) hI
  have hgain : deficiency T A ≤ deficiency T (A ∪ B) := by
    have hg := gain T A B
    change ((A ∩ B).card : ℤ)-((neighborhood (A ∩ B) \ U).card : ℤ) ≤
      (B.card : ℤ)-((neighborhood B \ U).card : ℤ) at hmax
    omega
  have hnew : MaximizesDeficiency F s T (A ∪ B) := by
    refine ⟨hAB,?_⟩
    intro C hC
    exact (hA.1.2 C hC).trans hgain
  exact Finset.Subset.trans Finset.subset_union_right (hA.2.2.1 (A ∪ B) hnew)
end RandomCNFClosure20

end
open RandomCNFDeficiency.LowerBound
open scoped Classical

set_option autoImplicit false



theorem solution
    {n : ℕ} (F : CNF n) (s D : ℝ) (hF : Criterion F s D)
    (T T' : Finset (Fin n)) (hTT' : T ⊆ T') (hT' : (T'.card : ℝ) ≤ D) :
    closure F s T ⊆ closure F s T'  := by
  exact RandomCNFClosure20.monotonicity F s D hF T T' hTT' hT'