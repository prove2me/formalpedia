-- Prove2me | solution 1 for QuantumBipartiteTesting.Bipartiteness.uniform_block_matching_contains
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T15:02:20.728207+00:00
-- url     : https://prove2.me/submissions/7970a8c4-f4b6-4845-bf89-dc0ca466582b

import Definitions.Def_DerandSq_PM
import Theorems.Thm_QuantumBipartiteTesting_Bipartiteness_uniform_matching_contains
import Definitions.Def_QuantumBipartiteTesting_Bipartiteness_Reduction

namespace QuantumBipartiteTesting.Bipartiteness.BlockMatchingProof
noncomputable section
open Finset
attribute [local instance] Classical.propDecidable Classical.decEq
set_option maxHeartbeats 500000
set_option maxRecDepth 2000
set_option backward.isDefEq.respectTransparency.types false

private def FiberPM (l s : ℕ) :=
  {h : Fin l × Fin s → Fin l × Fin s //
    ∀ p, h (h p) = p ∧ h p ≠ p ∧ (h p).1 = p.1}

private def FiberBlock {l s : ℕ} (h : FiberPM l s) (j : Fin l) (x : Fin s) : Fin s :=
  (h.val (j,x)).2

private lemma fiber_pair {l s : ℕ} (h : FiberPM l s) (j : Fin l) (x : Fin s) :
    h.val (j,x) = (j,FiberBlock h j x) := Prod.ext (h.property (j,x)).2.2 rfl

private lemma fiber_involutive {l s : ℕ} (h : FiberPM l s) (j : Fin l) :
    Function.Involutive (FiberBlock h j) := by
  intro x
  have hh := congrArg Prod.snd (h.property (j,x)).1
  rw [fiber_pair h j x] at hh
  exact hh

private def fiberFamilyEquiv (l s : ℕ) : FiberPM l s ≃ (Fin l → DerandSq.PM s) where
  toFun h j := ⟨(fiber_involutive h j).toPerm (FiberBlock h j),fun x => by
    refine ⟨fiber_involutive h j x,?_⟩
    intro heq
    apply (h.property (j,x)).2.1
    change FiberBlock h j x = x at heq
    rw [fiber_pair,heq]⟩
  invFun τ := ⟨fun p => (p.1,(τ p.1).val p.2),fun p => by
    refine ⟨?_,?_,rfl⟩
    · exact Prod.ext rfl ((τ p.1).property p.2).1
    · intro h
      exact ((τ p.1).property p.2).2 (congrArg Prod.snd h)⟩
  left_inv h := by
    apply Subtype.ext
    funext p
    exact (fiber_pair h p.1 p.2).symm
  right_inv τ := by
    funext j
    apply Subtype.ext
    apply Equiv.ext
    intro x
    rfl

private lemma blocksize_eq (l s : ℕ) (hl : 0 < l) : l*s/l = s := Nat.mul_div_cancel_left s hl

private lemma coordinate_first {l s : ℕ} (v : Fin (l*s)) :
    (finProdFinEquiv.symm v : Fin l × Fin s).1.val = v.val/s := rfl

private lemma conjugate_matching_iff (l s : ℕ) (hl : 0 < l)
    (h : Fin l × Fin s → Fin l × Fin s) :
    (∀ p, h (h p) = p ∧ h p ≠ p ∧ (h p).1 = p.1) ↔
      (fun v => finProdFinEquiv (h (finProdFinEquiv.symm v))) ∈ Matchings (l*s) l := by
  simp only [Matchings,mem_filter,mem_univ,true_and,blocksize_eq l s hl]
  constructor
  · intro hh
    constructor
    · intro v
      constructor
      · simpa only [Equiv.symm_apply_apply,Equiv.apply_symm_apply] using
          congrArg finProdFinEquiv (hh (finProdFinEquiv.symm v)).1
      · intro heq
        apply (hh (finProdFinEquiv.symm v)).2.1
        exact finProdFinEquiv.injective (heq.trans (finProdFinEquiv.apply_symm_apply v).symm)
    · intro v
      have heq := congrArg Fin.val (hh (finProdFinEquiv.symm v)).2.2
      simpa only [← coordinate_first,Equiv.symm_apply_apply] using heq
  · rintro ⟨hinv,hblock⟩ p
    have hp := hinv (finProdFinEquiv p)
    have hfirst := hblock (finProdFinEquiv p)
    refine ⟨?_,?_,?_⟩
    · apply finProdFinEquiv.injective
      simpa only [Equiv.symm_apply_apply] using hp.1
    · intro heq
      apply hp.2
      simpa only [Equiv.symm_apply_apply,heq]
    · apply Fin.ext
      simpa only [← coordinate_first,Equiv.symm_apply_apply] using hfirst

private def blockedMatchingEquiv (l s : ℕ) (hl : 0 < l) :
    FiberPM l s ≃ {h // h ∈ Matchings (l*s) l} :=
  (Equiv.arrowCongr finProdFinEquiv finProdFinEquiv).subtypeEquiv
    (conjugate_matching_iff l s hl)

private lemma average_equiv {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (f : β → ℝ) : Average univ (fun x => f (e x)) = Average univ f := by
  unfold Average
  rw [card_univ,card_univ,Fintype.card_congr e]
  congr 1
  exact e.sum_comp f

private lemma average_product {I α : Type*} [Fintype I] [Fintype α] [DecidableEq I]
    (f : I → α → ℝ) :
    Average univ (fun x : I → α => ∏ i, f i (x i)) = ∏ i, Average univ (f i) := by
  unfold Average
  simp only [card_univ,Fintype.card_fun]
  rw [← Fintype.prod_sum f,Finset.prod_div_distrib]
  simp

private def matchingFamilyEquiv (l s : ℕ) (hl : 0 < l) :
    {h // h ∈ Matchings (l*s) l} ≃ (Fin l → DerandSq.PM s) :=
  (blockedMatchingEquiv l s hl).symm.trans (fiberFamilyEquiv l s)

private lemma matchingFamily_apply {l s : ℕ} (hl : 0 < l)
    (h : {h // h ∈ Matchings (l*s) l}) (j : Fin l) (x y : Fin s) :
    ((matchingFamilyEquiv l s hl h) j).val x = y ↔
      h.val (finProdFinEquiv (j,x)) = finProdFinEquiv (j,y) := by
  change (finProdFinEquiv.symm (h.val (finProdFinEquiv (j,x)))).2 = y ↔ _
  have hp := ((blockedMatchingEquiv l s hl).symm h).property (j,x)
  change (fun p => finProdFinEquiv.symm (h.val (finProdFinEquiv p)))
    ((fun p => finProdFinEquiv.symm (h.val (finProdFinEquiv p))) (j,x)) = (j,x) ∧
    _ ∧ (finProdFinEquiv.symm (h.val (finProdFinEquiv (j,x)))).1 = j at hp
  constructor
  · intro heq
    apply finProdFinEquiv.symm.injective
    rw [Equiv.symm_apply_apply]
    exact Prod.ext hp.2.2 heq
  · intro heq
    rw [heq,Equiv.symm_apply_apply]

private lemma block_event_probability (l s : ℕ) (hl : 0 < l) (hs : Even s)
    (E : Fin l → Finset (Sym2 (Fin s)))
    (hloop : ∀ j, ∀ p ∈ E j, ¬ p.IsDiag)
    (hdisj : ∀ j, ∀ p ∈ E j, ∀ q ∈ E j, (∃ x, x ∈ p ∧ x ∈ q) → p = q) :
    Average univ (fun h : {h // h ∈ Matchings (l*s) l} =>
      if ∀ j a b, s(a,b) ∈ E j → h.val (finProdFinEquiv (j,a)) = finProdFinEquiv (j,b) then (1:ℝ) else 0) =
      ∏ j, ∏ a ∈ range (E j).card, ((s:ℝ)-2*a-1)⁻¹ := by
  let e := matchingFamilyEquiv l s hl
  rw [← average_equiv e.symm]
  have heq (τ : Fin l → DerandSq.PM s) :
      (∀ j a b, s(a,b) ∈ E j → (e.symm τ).val (finProdFinEquiv (j,a)) = finProdFinEquiv (j,b)) ↔
      (∀ j a b, s(a,b) ∈ E j → (τ j).val a = b) := by
    have hh (j : Fin l) (a b : Fin s) := matchingFamily_apply hl (e.symm τ) j a b
    simp only [← hh,e,Equiv.apply_symm_apply]
  simp_rw [heq]
  have hb (τ : Fin l → DerandSq.PM s) :
      (if ∀ j a b, s(a,b) ∈ E j → (τ j).val a = b then (1:ℝ) else 0) =
      ∏ j, if ∀ a b, s(a,b) ∈ E j → (τ j).val a = b then (1:ℝ) else 0 := by
    by_cases h : ∀ j a b, s(a,b) ∈ E j → (τ j).val a = b
    · rw [if_pos h]
      symm
      apply prod_eq_one
      intro j hj
      exact if_pos (h j)
    · rw [if_neg h]
      symm
      obtain ⟨j,hj⟩ := not_forall.mp h
      apply Finset.prod_eq_zero (mem_univ j)
      exact if_neg hj
  simp_rw [hb]
  let f := fun j (σ : DerandSq.PM s) => if ∀ a b, s(a,b) ∈ E j → σ.val a = b then (1:ℝ) else 0
  have hfun : (fun τ : Fin l → DerandSq.PM s =>
      ∏ j, if ∀ a b, s(a,b) ∈ E j → (τ j).val a = b then (1:ℝ) else 0) =
      fun τ => ∏ j, f j (τ j) := by
    funext τ
    apply prod_congr rfl
    intro j hj
    rfl
  rw [hfun]
  calc
    _ = ∏ j, Average univ (f j) := average_product f
    _ = _ := by
      apply prod_congr rfl
      intro j hj
      have hh := uniform_matching_contains s hs (E j) (hloop j) (hdisj j)
      convert hh using 2

private lemma average_subtype {α : Type*} (s : Finset α) (f : α → ℝ) :
    Average s f = Average univ (fun x : s => f x.val) := by
  simp only [Average,card_univ,Fintype.card_coe,Finset.sum_coe_sort]

end
end QuantumBipartiteTesting.Bipartiteness.BlockMatchingProof

open QuantumBipartiteTesting.Bipartiteness
open QuantumBipartiteTesting.Bipartiteness.BlockMatchingProof
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

theorem solution (l s : ℕ) (hl : 0 < l) (hs : Even s)
    (E : Fin l → Finset (Sym2 (Fin s)))
    (hloop : ∀ j, ∀ p ∈ E j, ¬ p.IsDiag)
    (hdisj : ∀ j, ∀ p ∈ E j, ∀ q ∈ E j, (∃ x, x ∈ p ∧ x ∈ q) → p = q) :
    Average (Matchings (l*s) l) (fun h =>
      if ∀ j a b, s(a,b) ∈ E j → h (finProdFinEquiv (j,a)) = finProdFinEquiv (j,b) then (1:ℝ) else 0) =
      ∏ j, ∏ a ∈ range (E j).card, ((s:ℝ)-2*a-1)⁻¹ := by
  rw [average_subtype]
  exact block_event_probability l s hl hs E hloop hdisj
end
