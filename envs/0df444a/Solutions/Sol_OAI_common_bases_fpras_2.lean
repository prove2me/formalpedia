-- Prove2me | solution 2 for OAI.common_bases_fpras
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T01:44:42.205444+00:00
-- url     : https://prove2.me/submissions/6f0dfaf3-6d77-4da7-be3d-505c00d749ce

import Mathlib
import Definitions.Def_CommonBasesFPRAS
import Definitions.Def_OAIQ2Mt000
import Theorems.Thm_OAI_CommonBasesFPRAS_MachineCode_frozen_machine
import Theorems.Thm_OAI_CommonBasesFPRAS_MachineCode_frozen_uniform_safe
import Theorems.Thm_OAI_CommonBasesFPRAS_rational_algorithm_success

section
-- module Solutions.OAIQ2_Mat.MatroidCounting_CommonBases
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CommonBasesFPRAS

section

section
open scoped RealInnerProductSpace BigOperators Matrix

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

open scoped BigOperators Classical

open Set

section PairedReduction
variable {α β : Type*}

lemma sum_eRank (M : Matroid α) (N : Matroid β) :
    (M.sum N).eRank = M.eRank + N.eRank := by
  obtain ⟨B,hB⟩ := M.exists_isBase
  obtain ⟨C,hC⟩ := N.exists_isBase
  have hBC : (M.sum N).IsBase (Sum.inl '' B ∪ Sum.inr '' C) := by
    rw [Matroid.sum_isBase_iff]
    simpa [Set.preimage_image_eq _ Sum.inl_injective,
      Set.preimage_image_eq _ Sum.inr_injective] using And.intro hB hC
  rw [← hBC.encard_eq_eRank, Set.encard_union_eq,
    Set.InjOn.encard_image, Set.InjOn.encard_image,
    hB.encard_eq_eRank, hC.encard_eq_eRank]
  · exact Sum.inr_injective.injOn
  · exact Sum.inl_injective.injOn
  · exact Set.disjoint_image_inl_image_inr

lemma transversal_isBase_iff (M₁ M₂ : Matroid α) (h₂ : M₂.E = Set.univ)
    (A : Set α) :
    (pairedMatroid M₁ M₂).IsBase (transversal A) ↔ M₁.IsBase A ∧ M₂.IsBase A := by
  simp only [pairedMatroid, Matroid.sum_isBase_iff, preimage_inl_transversal,
    preimage_inr_transversal, Matroid.dual_isBase_iff', h₂,
    ← Set.compl_eq_univ_sdiff, compl_compl, Set.subset_univ, and_true]

lemma paired_eRank [Fintype α] (M₁ M₂ : Matroid α) (h₂ : M₂.E = Set.univ)
    (hr : M₁.eRank = M₂.eRank) :
    (pairedMatroid M₁ M₂).eRank = (Fintype.card α : ℕ∞) := by
  rw [pairedMatroid, sum_eRank,hr, M₂.eRank_add_eRank_dual,h₂,
    Set.encard_univ, ENat.card_eq_coe_fintype_card]

lemma transversal_encard [Fintype α] (A : Set α) :
    (transversal A).encard = (Fintype.card α : ℕ∞) := by
  rw [transversal, Set.encard_union_eq,
    Set.InjOn.encard_image, Set.InjOn.encard_image,
    ← Set.encard_union_eq disjoint_compl_right, union_compl_self, Set.encard_univ,
    ENat.card_eq_coe_fintype_card]
  · exact Sum.inr_injective.injOn
  · exact Sum.inl_injective.injOn
  · exact Set.disjoint_image_inl_image_inr

end PairedReduction

open scoped BigOperators Classical

open scoped BigOperators Classical
lemma subsetDeficiency_zero {n : ℕ} (M₁ M₂ : Matroid (Fin n))
    (hE₂ : M₂.E=Set.univ) (hr : M₁.eRank=M₂.eRank) (A : Set (Fin n)) :
    subsetDeficiency M₁ M₂ A=0 ↔ M₁.IsBase A ∧ M₂.IsBase A := by
  have hR : (pairedMatroid M₁ M₂).eRank=(n:ℕ∞) := by simpa using paired_eRank M₁ M₂ hE₂ hr
  have hk : ((pairedMatroid M₁ M₂).eRk (transversal A)).toNat≤n :=
    ENat.toNat_le_of_le_natCast (by rw [← hR]; exact Matroid.eRk_le_eRank _ _)
  rw [← transversal_isBase_iff M₁ M₂ hE₂ A]
  constructor
  · intro hd
    have hn : ((pairedMatroid M₁ M₂).eRk (transversal A)).toNat=n := by unfold subsetDeficiency at hd; omega
    have he : (pairedMatroid M₁ M₂).eRk (transversal A)=(n:ℕ∞) := by
      calc
        _ = (((pairedMatroid M₁ M₂).eRk (transversal A)).toNat:ℕ∞) :=
          (ENat.natCast_toNat (Matroid.isRkFinite_set _ _).eRk_lt_top.ne).symm
        _ = _ := congrArg (fun k : ℕ => (k:ℕ∞)) hn
    have hi : (pairedMatroid M₁ M₂).Indep (transversal A) := by
      apply (Matroid.indep_iff_eRk_eq_encard_of_finite (Set.toFinite _)).mpr
      rw [he,transversal_encard,Fintype.card_fin]
    exact hi.isBase_of_eRk_ge (Set.toFinite _) (by rw [he,hR])
  · intro h
    unfold subsetDeficiency
    rw [h.eRk_eq_eRank,hR,ENat.toNat_natCast,Nat.sub_self]

open scoped BigOperators Classical
namespace FiniteChain
open scoped BigOperators Classical
variable {X : Type*} [sectionInstance101 : Fintype X]
universe u

omit sectionInstance101 in
lemma Sample.toList_length [Fintype X] {k : ℕ} (v : Sample X k) : v.toList.length=k+1 := by
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg Nat.succ (ih v.2)
end FiniteChain
section ActualHistoryEstimate
open scoped BigOperators Classical
variable (n : ℕ) (N L : ℕ) (M : Matroid (Fin n ⊕ Fin n))
lemma empirical_nonneg {Γ : Type*} (H : Set Γ → ℝ) (hH : ∀ S,0 ≤ H S) (l : List (Set Γ)) :
    0 ≤ empirical H l := by
  unfold empirical
  apply div_nonneg _ (Nat.cast_nonneg _)
  exact List.sum_nonneg (fun x hx => by obtain ⟨S,hS,rfl⟩ := List.mem_map.mp hx; exact hH S)
lemma empiricalRatio_nonneg {Γ : Type*} [Fintype Γ] [DecidableEq Γ]
    (gs : List (Γ × Γ)) (g : Set Γ → ℝ) (hg : ∀ S,0 ≤ g S) (l : List (Set Γ)) :
    0 ≤ empiricalRatio gs g l := by
  unfold empiricalRatio
  apply div_nonneg
  · apply empirical_nonneg; intro S; unfold plainObservable; split_ifs; exact hg S; rfl
  · apply empirical_nonneg; intro S; unfold plainObservable; split_ifs <;> norm_num
lemma historyEstimate_nonneg (hn : 0<n) (h : List (PhaseSample n N)) :
    0 ≤ historyEstimate n N L M h := by
  apply mul_nonneg (by positivity)
  apply Finset.prod_nonneg
  intro j _
  exact empiricalRatio_nonneg _ _ (fun S => pow_nonneg (le_trans (by norm_num) (annealRho_bounds n hn).1) _) _
end ActualHistoryEstimate
section WitnessRestart
open scoped BigOperators Classical
variable (n : ℕ) (hn : 0<n) (M₁ M₂ : Matroid (Fin n))
local notation "GS" => pairedSlots n
lemma witnessed_iff_common_base (hE₂ : M₂.E=Set.univ) (hr : M₁.eRank=M₂.eRank) (x : PlainIndex GS) :
    Witnessed n M₁ M₂ x ↔ M₁.IsBase (Sum.inl ⁻¹' x.val.val) ∧ M₂.IsBase (Sum.inl ⁻¹' x.val.val) := by
  unfold Witnessed
  rw [plain_eq_transversal n x.val.val x.property]
  simpa only [preimage_inl_transversal,subsetDeficiency] using subsetDeficiency_zero M₁ M₂ hE₂ hr (Sum.inl ⁻¹' x.val.val)
lemma witnessed_count_pos (hE₂ : M₂.E=Set.univ) (hr : M₁.eRank=M₂.eRank) (x : PlainIndex GS)
    (hx : Witnessed n M₁ M₂ x) : 0<commonBaseCount M₁ M₂ := by
  obtain ⟨h₁,h₂⟩ := (witnessed_iff_common_base n M₁ M₂ hE₂ hr x).mp hx
  unfold commonBaseCount
  rw [Nat.card_eq_fintype_card]
  apply Fintype.card_pos_iff.mpr
  exact ⟨⟨(Sum.inl ⁻¹' x.val.val).toFinset,by simpa using And.intro h₁ h₂⟩⟩
end WitnessRestart
open scoped BigOperators Classical
variable (n : ℕ) (hn : 0<n) (M₁ M₂ : Matroid (Fin n)) (N L : ℕ)
local notation "K" => pairedMatroid M₁ M₂
local notation "GS" => pairedSlots n
include hn in
lemma guardedEstimate_nonneg (h : List (PhaseSample n N)) (x : PlainIndex GS) :
    0 ≤ guardedEstimate n M₁ M₂ N L h x := by
  unfold guardedEstimate
  split_ifs
  · exact historyEstimate_nonneg n N L K hn h
  · rfl
lemma guardedEstimate_zero (hE₂ : M₂.E=Set.univ) (hr : M₁.eRank=M₂.eRank)
    (hZ : commonBaseCount M₁ M₂=0) (h : List (PhaseSample n N)) (x : PlainIndex GS) :
    guardedEstimate n M₁ M₂ N L h x=0 := by
  unfold guardedEstimate
  apply ite_eq_right
  intro hx
  have hp := witnessed_count_pos n M₁ M₂ hE₂ hr x hx
  omega

end

section

open scoped BigOperators Classical
lemma uniformAverage_equiv {X Y : Type*} [Fintype X] [Fintype Y]
    (e : X ≃ Y) (f : Y → ℝ) : uniformAverage (fun x => f (e x))=uniformAverage f := by
  rw [uniformAverage,uniformAverage,e.sum_comp,Fintype.card_congr e]
lemma uniformAverage_const {X : Type*} [Fintype X] [Nonempty X] (r : ℝ) :
    uniformAverage (fun _ : X => r)=r := by
  have h : (Fintype.card X:ℝ)≠0 := by exact_mod_cast ne_of_gt (Fintype.card_pos)
  simp [uniformAverage,h]
lemma uniformAverage_add {X : Type*} [Fintype X] (f g : X → ℝ) :
    uniformAverage (fun x => f x+g x)=uniformAverage f+uniformAverage g := by
  simp [uniformAverage,Finset.sum_add_distrib,add_div]
lemma uniformAverage_mul_left {X : Type*} [Fintype X] (r : ℝ) (f : X → ℝ) :
    uniformAverage (fun x => r*f x)=r*uniformAverage f := by
  simp [uniformAverage,← Finset.mul_sum,mul_div_assoc]
lemma uniformAverage_prod {X Y : Type*} [Fintype X] [Fintype Y] (f : X × Y → ℝ) :
    uniformAverage f=uniformAverage (fun x => uniformAverage (fun y => f (x,y))) := by
  simp only [uniformAverage,Fintype.sum_prod_type,Fintype.card_prod,Nat.cast_mul]
  rw [← Finset.sum_div]
  ring
lemma uniformAverage_fin_succ {X : Type*} [Fintype X] (D : ℕ)
    (f : (Fin (D+1) → X) → ℝ) :
    uniformAverage f=uniformAverage (fun x => uniformAverage (fun rest => f (Fin.cons x rest))) := by
  rw [← uniformAverage_equiv (Fin.consEquiv (fun _ : Fin (D+1) => X)) f,uniformAverage_prod]
  rfl

lemma acceptedCard (v T : ℕ) (hv : v≤T) :
    Fintype.card {x : Fin T // x.val < v}=v := by
  let e : {x : Fin T // x.val < v} ≃ Fin v :=
    { toFun := fun x => ⟨x.val.val,x.property⟩
      invFun := fun x => ⟨⟨x.val,lt_of_lt_of_le x.isLt hv⟩,x.isLt⟩
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl }
  simpa using Fintype.card_congr e
lemma rejectedCard (v T : ℕ) (hv : v≤T) :
    Fintype.card {x : Fin T // ¬x.val < v}=T-v := by
  rw [Fintype.card_subtype_compl,acceptedCard v T hv,Fintype.card_fin]
lemma sum_ite_count {X : Type*} [Fintype X] (p : X → Prop) [DecidablePred p] (r : ℝ) :
    (∑ x,if p x then r else 0)=(Fintype.card {x // p x}:ℝ)*r := by
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const,nsmul_eq_mul]
  congr 1
  exact_mod_cast (Fintype.card_subtype p).symm
lemma one_trial_none (v h : ℕ) (hv : v≤2^h) (r : ℝ) :
    uniformAverage (fun bits : BitWord h => if (wordEquiv h bits).val < v then 0 else r)=
      rejectionRate v h*r := by
  rw [uniformAverage_equiv (wordEquiv h) (fun x => if x.val<v then 0 else r)]
  unfold uniformAverage rejectionRate
  have he : (∑ x : Fin (2^h),if x.val<v then (0:ℝ) else r)=(2^h-v:ℕ)*r := by
    calc
      _ = ∑ x : Fin (2^h),if ¬x.val<v then r else 0 := by
        apply Finset.sum_congr rfl
        intro x _
        by_cases hx : x.val<v <;> simp [hx]
      _ = _ := by rw [sum_ite_count,rejectedCard _ _ hv]
  rw [he,Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat]
  ring
lemma one_trial_some (v h : ℕ) (hv : v≤2^h) (a : Fin v) (r : ℝ) :
    uniformAverage (fun bits : BitWord h =>
      if hx : (wordEquiv h bits).val<v then
        (if (⟨(wordEquiv h bits).val,hx⟩ : Fin v)=a then (1:ℝ) else 0)
      else r) = 1/(2:ℝ)^h+rejectionRate v h*r := by
  let aT : Fin (2^h) := ⟨a.val,lt_of_lt_of_le a.isLt hv⟩
  have he : (fun bits : BitWord h =>
      if hx : (wordEquiv h bits).val<v then
        (if (⟨(wordEquiv h bits).val,hx⟩ : Fin v)=a then (1:ℝ) else 0)
      else r) = fun bits => (if wordEquiv h bits=aT then 1 else 0)+
        (if (wordEquiv h bits).val<v then 0 else r) := by
    funext bits
    by_cases hx : (wordEquiv h bits).val<v
    · have he : (⟨(wordEquiv h bits).val,hx⟩ : Fin v)=a ↔ wordEquiv h bits=aT := by
        simp only [Fin.ext_iff,aT]
      simp [hx,he]
    · have he : wordEquiv h bits≠aT := by
        intro hh
        have ht : (wordEquiv h bits).val=a.val := congrArg Fin.val hh
        exact hx (ht ▸ a.isLt)
      simp [hx,he]
  rw [he,uniformAverage_add,one_trial_none v h hv r]
  congr 1
  rw [uniformAverage_equiv (wordEquiv h) (fun x => if x=aT then 1 else 0)]
  simp [uniformAverage,aT]
lemma boundedUniform_failure (v h D : ℕ) (hv : v≤2^h) :
    uniformAverage (fun bits => if boundedUniform v h D bits=none then (1:ℝ) else 0)=
      rejectionRate v h^D := by
  induction D with
  | zero => simp [boundedUniform,uniformAverage_const]
  | succ D ih =>
    rw [uniformAverage_fin_succ]
    have he : (fun x : BitWord h => uniformAverage (fun rest : Fin D → BitWord h =>
        if boundedUniform v h (D+1) (Fin.cons x rest)=none then (1:ℝ) else 0)) =
        fun x => if (wordEquiv h x).val<v then 0 else rejectionRate v h^D := by
      funext x
      by_cases hx : (wordEquiv h x).val<v
      · simp only [boundedUniform,Fin.cons_zero,dite_eq_left hx,Option.some_ne_none,ite_false,ite_eq_left hx]
        try simp only [Fin.ext_iff]
        apply uniformAverage_const
      · simpa [boundedUniform,hx] using ih
    rw [he,one_trial_none v h hv,pow_succ']
lemma rejectionRate_bounds (v h : ℕ) (hv : v≤2^h) (hhalf : 2^h≤2*v) :
    0≤rejectionRate v h ∧ rejectionRate v h≤1/2 := by
  have hT : (0:ℝ)<(2:ℝ)^h := by positivity
  have hc : ((2^h-v:ℕ):ℝ)=(2:ℝ)^h-v := by rw [Nat.cast_sub hv,Nat.cast_pow,Nat.cast_ofNat]
  have hh : (2:ℝ)^h≤2*(v:ℝ) := by exact_mod_cast hhalf
  unfold rejectionRate
  constructor
  · positivity
  · rw [hc,div_le_iff₀ hT]; linarith
lemma clog_trial_size (v : ℕ) (hv : 0<v) : v≤2^Nat.clog 2 v ∧ 2^Nat.clog 2 v≤2*v := by
  refine ⟨Nat.le_pow_clog (by norm_num) v,?_⟩
  by_cases h : v=1
  · subst v; norm_num
  have hv' : 1<v := by omega
  have hh := Nat.pow_pred_clog_lt_self (by norm_num : 1<2) hv'
  have hc := Nat.clog_pos (by norm_num : 1<2) hv'
  have hp : Nat.clog 2 v=(Nat.clog 2 v).pred+1 := by exact (Nat.succ_pred_eq_of_pos hc).symm
  rw [hp,pow_succ]
  omega
lemma boundedUniform_probability (v h D : ℕ) (hv : v ≤ 2^h) (hv0 : 0 < v) (a : Fin v) :
    uniformAverage (fun bits => if boundedUniform v h D bits=some a then (1:ℝ) else 0)=
      (1-rejectionRate v h^D)/(v:ℝ) := by
  have hv' : (v:ℝ)≠0 := by exact_mod_cast ne_of_gt hv0
  have hT : (2:ℝ)^h≠0 := by positivity
  induction D with
  | zero => simp [boundedUniform,uniformAverage_const]
  | succ D ih =>
    rw [uniformAverage_fin_succ]
    have he : (fun x : BitWord h => uniformAverage (fun rest : Fin D → BitWord h =>
        if boundedUniform v h (D+1) (Fin.cons x rest)=some a then (1:ℝ) else 0)) =
        fun x => if hx : (wordEquiv h x).val<v then
          (if (⟨(wordEquiv h x).val,hx⟩ : Fin v)=a then 1 else 0)
          else (1-rejectionRate v h^D)/(v:ℝ) := by
      funext x
      by_cases hx : (wordEquiv h x).val<v
      · simp only [boundedUniform,Fin.cons_zero,dite_eq_left hx,Option.some.injEq,]
        try simp only [Fin.ext_iff]
        apply uniformAverage_const
      · simpa [boundedUniform,hx] using ih
    rw [he,one_trial_some v h hv]
    have hr : rejectionRate v h=1-(v:ℝ)/(2:ℝ)^h := by
      unfold rejectionRate
      rw [Nat.cast_sub hv,Nat.cast_pow,Nat.cast_ofNat]
      field_simp
    rw [pow_succ]
    calc
      _ = ((v:ℝ)/(2:ℝ)^h+rejectionRate v h-rejectionRate v h^D*rejectionRate v h)/v := by
        field_simp ; ring
      _ = _ := by rw [hr]; ring
lemma uniformAverage_sum {X J : Type*} [Fintype X] [Fintype J] (f : J → X → ℝ) :
    uniformAverage (fun x => ∑ j,f j x)=∑ j,uniformAverage (f j) := by
  unfold uniformAverage
  rw [Finset.sum_comm,Finset.sum_div]

lemma boundedUniform_law (v h D : ℕ) (hv : v ≤ 2^h) (hv0 : 0 < v) (φ : Option (Fin v) → ℝ) :
    uniformAverage (fun bits => φ (boundedUniform v h D bits)) =
      rejectionRate v h^D*φ none + (1-rejectionRate v h^D)*uniformAverage (fun a => φ (some a)) := by
  have he : (fun bits => φ (boundedUniform v h D bits)) = fun bits =>
      φ none*(if boundedUniform v h D bits=none then 1 else 0) +
        ∑ a : Fin v,φ (some a)*(if boundedUniform v h D bits=some a then 1 else 0) := by
    funext bits
    cases e : boundedUniform v h D bits with
    | none => simp
    | some a => simp
  rw [he,uniformAverage_add,uniformAverage_mul_left,boundedUniform_failure v h D hv,
    uniformAverage_sum]
  simp_rw [uniformAverage_mul_left,boundedUniform_probability v h D hv hv0]
  rw [← Finset.sum_mul]
  unfold uniformAverage
  rw [Fintype.card_fin]
  ring

lemma uniformAverage_nonneg {X : Type*} [Fintype X] (f : X → ℝ)
    (hf : ∀ x,0≤f x) : 0≤uniformAverage f := by
  exact div_nonneg (Finset.sum_nonneg (fun x _ => hf x)) (Nat.cast_nonneg _)
lemma uniformAverage_mono {X : Type*} [Fintype X] (f g : X → ℝ)
    (hfg : ∀ x,f x≤g x) : uniformAverage f≤uniformAverage g := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun x _ => hfg x)) (Nat.cast_nonneg _)
lemma uniformAverage_sub_const {X : Type*} [Fintype X] [Nonempty X] (f : X → ℝ) (r : ℝ) :
    uniformAverage (fun x => f x-r)=uniformAverage f-r := by
  unfold uniformAverage
  rw [Finset.sum_sub_distrib,sub_div]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  have h : (Fintype.card X:ℝ)≠0 := by exact_mod_cast ne_of_gt (Fintype.card_pos)
  field_simp

lemma uniformAverage_bitPrefix (h H : ℕ) (hh : h≤H) (φ : BitWord h → ℝ) :
    uniformAverage (fun w => φ (bitPrefix h H hh w))=uniformAverage φ := by
  obtain ⟨t,rfl⟩ := Nat.exists_eq_add_of_le hh
  rw [← uniformAverage_equiv (Fin.appendEquiv h t) (fun w => φ (bitPrefix h (h+t) hh w)),uniformAverage_prod]
  have he : ∀ a : BitWord h,∀ b : BitWord t,bitPrefix h (h+t) hh ((Fin.appendEquiv h t) (a,b))=a := by
    intro a b
    funext i
    change Fin.append a b (Fin.castAdd t i)=a i
    simp
  simp_rw [he,uniformAverage_const]
lemma uniformAverage_prefixTrials (h H D : ℕ) (hh : h≤H)
    (φ : (Fin D → BitWord h) → ℝ) :
    uniformAverage (fun w : Fin D → BitWord H => φ (fun d => bitPrefix h H hh (w d)))=uniformAverage φ := by
  induction D with
  | zero =>
    have he : ∀ w : Fin 0 → BitWord H,(fun d => bitPrefix h H hh (w d))=(fun d : Fin 0 => Fin.elim0 d) := by
      intro w; funext d; exact Fin.elim0 d
    have hf : ∀ w : Fin 0 → BitWord h,w=(fun d : Fin 0 => Fin.elim0 d) := by
      intro w; funext d; exact Fin.elim0 d
    simp_rw [he]
    rw [uniformAverage_const]
    conv_rhs => arg 1; ext w; rw [hf w]
    rw [uniformAverage_const]
  | succ D ih =>
    rw [uniformAverage_fin_succ,uniformAverage_fin_succ]
    have he : ∀ x : BitWord H,∀ xs : Fin D → BitWord H,
        (fun d : Fin (D+1) => bitPrefix h H hh ((Fin.cons x xs : Fin (D+1) → BitWord H) d))=
        Fin.cons (bitPrefix h H hh x) (fun d => bitPrefix h H hh (xs d)) := by
      intro x xs; funext d; refine Fin.cases ?_ (fun i => ?_) d <;> rfl
    simp_rw [he]
    have hhφ : ∀ x : BitWord H,
        uniformAverage (fun xs : Fin D → BitWord H => φ (Fin.cons (bitPrefix h H hh x) (fun d => bitPrefix h H hh (xs d))))=
        uniformAverage (fun xs : Fin D → BitWord h => φ (Fin.cons (bitPrefix h H hh x) xs)) := by
      intro x
      exact ih (fun xs => φ (Fin.cons (bitPrefix h H hh x) xs))
    simp_rw [hhφ]
    exact uniformAverage_bitPrefix h H hh (fun x => uniformAverage (fun xs => φ (Fin.cons x xs)))

namespace DrawTree

section
open scoped BigOperators Classical
variable {A : Type*}
lemma expectation_le_one (φ : A → ℝ) (hφ : ∀ a,φ a≤1) (t : DrawTree A) :
    t.expectation φ≤1 := by
  induction t with
  | leaf a => exact hφ a
  | draw v k ih =>
    have h := uniformAverage_mono _ (fun _ : Fin (v+1) => 1) ih
    simpa only [expectation,uniformAverage_const] using h

lemma run_draw_average (H D M v : ℕ) (k : Fin (v+1) → DrawTree A)
    (hh : Nat.clog 2 (v+1)≤H) (φ : A → ℝ) :
    uniformAverage (fun bits => optionValue φ (run H D (M+1) (.draw v k) bits))=
      (1-rejectionRate (v+1) (Nat.clog 2 (v+1))^D)*
        uniformAverage (fun a : Fin (v+1) => uniformAverage
          (fun rest => optionValue φ (run H D M (k a) rest))) := by
  rw [uniformAverage_fin_succ]
  simp only [run,dite_eq_left hh,Fin.cons_zero,Fin.tail_cons]
  let ψ : Option (Fin (v+1)) → ℝ := fun z => match z with
    | none => 0
    | some a => uniformAverage (fun rest => optionValue φ (run H D M (k a) rest))
  have he : (fun x : Fin D → BitWord H => uniformAverage
      (fun rest : Fin M → Fin D → BitWord H => optionValue φ
        (match boundedUniform (v+1) (Nat.clog 2 (v+1)) D
          (fun d => bitPrefix _ H hh (x d)) with
         | none => none
         | some a => run H D M (k a) rest))) =
      fun x => ψ (boundedUniform (v+1) (Nat.clog 2 (v+1)) D
          (fun d => bitPrefix _ H hh (x d))) := by
    funext x
    cases hz : boundedUniform (v+1) (Nat.clog 2 (v+1)) D
      (fun d => bitPrefix _ H hh (x d)) with
    | none => exact uniformAverage_const 0
    | some a => rfl
  erw [he,uniformAverage_prefixTrials _ _ D hh (fun w => ψ (boundedUniform (v+1) (Nat.clog 2 (v+1)) D w))]
  rw [boundedUniform_law _ _ _ (clog_trial_size _ (by omega)).1 (by omega)]
  simp only [ψ,mul_zero,zero_add]

theorem run_lower (H D M : ℕ) (t : DrawTree A) (ht : Fits H M t)
    (φ : A → ℝ) (_ : ∀ a,0≤φ a) (hφ1 : ∀ a,φ a≤1) :
    t.expectation φ-(M:ℝ)*(1/2:ℝ)^D ≤
      uniformAverage (fun bits => optionValue φ (run H D M t bits)) := by
  induction M generalizing t with
  | zero =>
    cases t with
    | leaf a => simp [run,optionValue,expectation,uniformAverage_const]
    | draw v k => exact False.elim ht
  | succ M ih =>
    cases t with
    | leaf a =>
      simp only [expectation,run,optionValue,uniformAverage_const]
      have h : 0 ≤ ((M+1:ℕ):ℝ)*(1/2:ℝ)^D := by positivity
      linarith
    | draw v k =>
      obtain ⟨hh,hk⟩ := ht
      rw [run_draw_average H D M v k hh φ]
      have hlocal := uniformAverage_mono
        (fun a => (k a).expectation φ-(M:ℝ)*(1/2:ℝ)^D)
        (fun a => uniformAverage (fun bits => optionValue φ (run H D M (k a) bits)))
        (fun a => ih (k a) (hk a))
      rw [uniformAverage_sub_const] at hlocal
      let r := rejectionRate (v+1) (Nat.clog 2 (v+1))^D
      have hb := rejectionRate_bounds (v+1) (Nat.clog 2 (v+1))
        (clog_trial_size _ (by omega)).1 (clog_trial_size _ (by omega)).2
      have hr0 : 0≤r := pow_nonneg hb.1 D
      have hr : r≤(1/2:ℝ)^D := pow_le_pow_left₀ hb.1 hb.2 D
      have hr1 : r≤1 := hr.trans (pow_le_one₀ (by norm_num) (by norm_num))
      have hE : uniformAverage (fun a => (k a).expectation φ)≤1 :=
        expectation_le_one φ hφ1 (.draw v k)
      have hmul := mul_le_mul_of_nonneg_left hlocal (sub_nonneg.mpr hr1)
      have hz : 0≤(M:ℝ)*(1/2:ℝ)^D := by positivity
      change _ ≤ (1-r)*_
      change uniformAverage (fun a => (k a).expectation φ)-((M+1:ℕ):ℝ)*(1/2:ℝ)^D ≤ _
      push_cast
      nlinarith [mul_nonneg hr0 hz,mul_nonneg hr0 (sub_nonneg.mpr hE)]
end
open scoped BigOperators Classical
variable {A B : Type*}
lemma fits_mono_steps (H M M' : ℕ) (hM : M≤M') (t : DrawTree A) (ht : Fits H M t) :
    Fits H M' t := by
  induction M generalizing M' t with
  | zero => cases t <;> simp_all [Fits]
  | succ M ih =>
    cases t with
    | leaf a => simp [Fits]
    | draw v f =>
      cases M' with
      | zero => omega
      | succ M' => exact ⟨ht.1,fun i => ih M' (by omega) (f i) (ht.2 i)⟩
lemma fits_bind (H M N : ℕ) (t : DrawTree A) (k : A → DrawTree B)
    (ht : Fits H M t) (hk : ∀ a,Fits H N (k a)) : Fits H (M+N) (t.bind k) := by
  induction M generalizing t with
  | zero => cases t with
    | leaf a => simpa only [bind,Nat.zero_add] using hk a
    | draw v f => exact False.elim ht
  | succ M ih =>
    cases t with
    | leaf a => exact fits_mono_steps H N (M+1+N) (by omega) (k a) (hk a)
    | draw v f =>
      have he : M+1+N=(M+N)+1 := by omega
      rw [he]
      exact ⟨ht.1,fun i => ih (f i) (ht.2 i)⟩

lemma rationalCoin_fits (a v H : ℕ) (hh : Nat.clog 2 (v+1)≤H) :
    Fits H 1 (rationalCoin a v) := ⟨hh,fun _ => trivial⟩
lemma bernoulli_fits (p : ℚ) (H : ℕ) (hh : Nat.clog 2 p.den≤H) :
    Fits H 1 (bernoulli p) := by
  unfold bernoulli
  apply rationalCoin_fits
  have hd : p.den-1+1=p.den := by have h := p.den_pos; omega
  simpa only [hd] using hh
end DrawTree

section RationalSampling
open scoped BigOperators Classical
variable {Γ : Type*} [sectionInstance112 : Fintype Γ] [sectionInstance113 : DecidableEq Γ]
omit sectionInstance112 sectionInstance113 in
lemma rationalEmpirical_cast [Fintype Γ] [DecidableEq Γ] (H : Set Γ → ℚ) (l : List (Set Γ)) :
    (rationalEmpirical H l:ℝ)=empirical (fun S => (H S:ℝ)) l := by
  simp [rationalEmpirical,empirical,Rat.cast_list_sum,List.map_map,Function.comp_def]
omit sectionInstance112 sectionInstance113 in
lemma rationalPlain_cast [Fintype Γ] [DecidableEq Γ] (gs : List (Γ × Γ)) (g : Set Γ → ℚ) (S : Set Γ) :
    (rationalPlain gs g S:ℝ)=plainObservable gs (fun S => (g S:ℝ)) S := by
  unfold rationalPlain plainObservable; split_ifs <;> simp
omit sectionInstance112 sectionInstance113 in
lemma rationalDefect_cast [Fintype Γ] [DecidableEq Γ] (gs : List (Γ × Γ)) (p r : Γ × Γ) (S : Set Γ) :
    (rationalDefect gs p r S:ℝ)=defectIndicator gs p r S := by
  unfold rationalDefect defectIndicator; split_ifs <;> simp
lemma rationalLearn_cast (gs : List (Γ × Γ))
    (w : (Γ × Γ) → (Γ × Γ) → ℚ) (l : List (Set Γ)) (p r : Γ × Γ) :
    (rationalLearn gs w l p r:ℝ)=learnedMultipliers gs (fun p r => (w p r:ℝ)) l p r := by
  unfold rationalLearn learnedMultipliers
  split_ifs <;> simp [rationalEmpirical_cast,rationalPlain_cast,rationalDefect_cast]
lemma rationalHistory_cast {X : Type*} (gs : List (Γ × Γ))
    (sample : X → List (Set Γ)) (h : List X) (p r : Γ × Γ) :
    (rationalHistory gs sample h p r:ℝ)=historyWeights gs sample h p r := by
  induction h using List.reverseRecOn generalizing p r with
  | nil => norm_num [rationalHistory,historyWeights]
  | append_singleton h x ih =>
    simp only [rationalHistory,List.foldl_append,List.foldl_cons,List.foldl_nil,historyWeights_snoc]
    rw [rationalLearn_cast]
    have he : (fun p r => ((h.foldl (fun w x => rationalLearn gs w (sample x)) (fun _ _ => 4)) p r:ℝ))=
        historyWeights gs sample h := by funext p r; exact ih p r
    rw [he]

lemma rationalRho_cast (n : ℕ) : (rationalRho n:ℝ)=annealRho n := by simp [rationalRho,annealRho]
lemma rationalRatio_cast (gs : List (Γ × Γ)) (g : Set Γ → ℚ) (l : List (Set Γ)) :
    (rationalRatio gs g l:ℝ)=empiricalRatio gs (fun S => (g S:ℝ)) l := by
  simp [rationalRatio,empiricalRatio,rationalEmpirical_cast,rationalPlain_cast]
end RationalSampling

namespace DrawTree
open scoped BigOperators Classical
lemma uniformChoice_fits (A : Type*) [Fintype A] [Nonempty A] (H : ℕ)
    (h : Nat.clog 2 (Fintype.card A)≤H) : Fits H 1 (uniformChoice A) := by
  unfold uniformChoice
  refine ⟨?_,fun _ => trivial⟩
  have he : Fintype.card A-1+1=Fintype.card A := by have hh := Fintype.card_pos (α := A); omega
  simpa only [he] using h
end DrawTree

namespace DrawTree
open scoped BigOperators Classical
variable {A B D : Type*}
lemma optionBind_fits (t : DrawTree (Option A)) (k : A → DrawTree (Option B))
    (H M N : ℕ) (ht : Fits H M t) (hk : ∀ a,Fits H N (k a)) :
    Fits H (M+N) (t.optionBind k) := by
  apply fits_bind H M N t _ ht
  intro a; cases a with
  | none => cases N <;> trivial
  | some a => exact hk a

lemma iterate_fits (t : A → DrawTree (Option A)) (H M k : ℕ)
    (ht : ∀ a,Fits H M (t a)) : ∀ a,Fits H (M*k) (iterate t k a) := by
  induction k with
  | zero => intro a; trivial
  | succ k ih =>
    intro a
    have h := optionBind_fits (iterate t k a) t H (M*k) M (ih a) ht
    simpa only [iterate,Nat.mul_succ] using h
end DrawTree

section DrawHitting
open scoped BigOperators Classical
variable {X : Type*} [sectionInstance116 : Fintype X]
variable (step : X → DrawTree X) (A : X → Prop)
omit sectionInstance116 in
lemma hittingTree_fits [Fintype X] (H M k : ℕ) (hs : ∀ x,DrawTree.Fits H M (step x)) :
    ∀ x,DrawTree.Fits H (M*k) (hittingTree step A k x) := by
  induction k with
  | zero => intro x; trivial
  | succ k ih =>
    intro x
    unfold hittingTree
    have h := DrawTree.fits_bind H M (M*k) (step x)
      (fun y => if hy : A y then DrawTree.leaf (some (⟨y,hy⟩ : FiniteChain.Inside A)) else hittingTree step A k y)
      (hs x) (by intro y; split_ifs; exacts [by cases M*k <;> trivial,ih y])
    simpa only [Nat.mul_succ,Nat.add_comm] using h
end DrawHitting
namespace DrawTree
open scoped BigOperators Classical
variable {X Y : Type*} [sectionInstance117 : Fintype X]
omit sectionInstance117 in
lemma map_fits [Fintype X] (t : DrawTree X) (f : X → Y) (H M : ℕ) (ht : Fits H M t) :
    Fits H M (t.map f) := by
  have h := fits_bind H M 0 t (fun x => .leaf (f x)) ht (fun _ => trivial)
  simpa only [map,Nat.add_zero] using h
lemma sample_fits (step : X → DrawTree X) (H M k : ℕ)
    (hs : ∀ x,Fits H M (step x)) (x : X) : Fits H (M*k) (sample step k x) := by
  induction k generalizing x with
  | zero => trivial
  | succ k ih =>
    unfold sample
    have h := fits_bind H M (M*k) (step x)
      (fun y => (sample step k y).map (fun v : FiniteChain.Sample X k => (x,v)))
      (hs x) (by intro y; exact map_fits _ _ H (M*k) (ih y))
    simpa only [FiniteChain.Sample,sample,Nat.mul_succ,Nat.add_comm] using h

end DrawTree
section DrawActual
open scoped BigOperators Classical
variable (n : ℕ) (hn : 0<n) (M : Matroid (Fin n ⊕ Fin n)) (N L : ℕ)
local notation "GS" => pairedSlots n
lemma rationalStored_cast (h : List (PhaseSample n N)) (j : ℕ) (p r) :
    (rationalStored n N h j p r:ℝ)=storedWeights n N h j p r := by
  exact rationalHistory_cast GS (observedSets n N) (h.take j) p r
end DrawActual
open scoped BigOperators Classical
variable (n : ℕ) (hn : 0<n) (M₁ M₂ : Matroid (Fin n)) (N L : ℕ)
local notation "K" => pairedMatroid M₁ M₂
local notation "GS" => pairedSlots n
lemma rationalEstimate_cast (h : List (PhaseSample n N)) :
    (rationalEstimate n M₁ M₂ N L h:ℝ)=historyEstimate n N L K h := by
  simp only [rationalEstimate,Rat.cast_mul,Rat.cast_pow,Rat.cast_ofNat,Rat.cast_prod,rationalRatio_cast,
    rationalRho_cast,historyEstimate]
lemma rationalGuard_cast (h : List (PhaseSample n N)) (x : PlainIndex GS) :
    (rationalGuard n M₁ M₂ N L h x:ℝ)=guardedEstimate n M₁ M₂ N L h x := by
  unfold rationalGuard guardedEstimate
  split_ifs <;> simp [rationalEstimate_cast]
include hn in
lemma rationalGuard_nonneg (h : List (PhaseSample n N)) (x : PlainIndex GS) :
    0≤rationalGuard n M₁ M₂ N L h x := by
  have hh := guardedEstimate_nonneg n hn M₁ M₂ N L h x
  rw [←rationalGuard_cast] at hh
  exact_mod_cast hh
lemma rationalGuard_zero (hE₂ : M₂.E=Set.univ) (hr : M₁.eRank=M₂.eRank)
    (hZ : commonBaseCount M₁ M₂=0) (h : List (PhaseSample n N)) (x : PlainIndex GS) :
    rationalGuard n M₁ M₂ N L h x=0 := by
  have hh := guardedEstimate_zero n M₁ M₂ N L hE₂ hr hZ h x
  rw [←rationalGuard_cast] at hh
  exact_mod_cast hh

end

open scoped BigOperators Classical

namespace RatBound
variable {q r : ℚ} {B D : ℕ}
lemma one_le (h : RatBound q B) : 1≤B := by
  obtain ⟨a,b,ha,hb,hpos,he⟩ := h; omega
lemma mono (h : RatBound q B) (hBD : B≤D) : RatBound q D := by
  obtain ⟨a,b,ha,hb,hpos,he⟩ := h
  exact ⟨a,b,ha.trans hBD,hb.trans hBD,hpos,he⟩
lemma nat (a B : ℕ) (ha : a≤B) (hB : 0<B) : RatBound (a:ℚ) B :=
  ⟨a,1,ha,hB,by omega,by simp⟩
lemma zero (B : ℕ) (hB : 0<B) : RatBound 0 B := by exact_mod_cast nat 0 B (by omega) hB
lemma one (B : ℕ) (hB : 0<B) : RatBound 1 B := by exact_mod_cast nat 1 B hB hB
lemma mul (hq : RatBound q B) (hr : RatBound r D) : RatBound (q*r) (B*D) := by
  obtain ⟨a,b,ha,hb,hpos,rfl⟩ := hq
  obtain ⟨c,d,hc,hd,hdpos,rfl⟩ := hr
  exact ⟨a*c,b*d,Nat.mul_le_mul ha hc,Nat.mul_le_mul hb hd,Nat.mul_pos hpos hdpos,by push_cast; ring⟩
lemma inv (hq : RatBound q B) : RatBound q⁻¹ B := by
  obtain ⟨a,b,ha,hb,hpos,rfl⟩ := hq
  by_cases hz : a=0
  · subst a; simpa using zero B (by omega)
  · exact ⟨b,a,hb,ha,Nat.pos_of_ne_zero hz,by simp [inv_div]⟩
lemma div (hq : RatBound q B) (hr : RatBound r D) : RatBound (q/r) (B*D) := by
  simpa only [div_eq_mul_inv] using hq.mul hr.inv
lemma pow (hq : RatBound q B) (k : ℕ) : RatBound (q^k) (B^k) := by
  induction k with
  | zero => simpa using one 1 (by decide)
  | succ k ih => simpa only [pow_succ] using ih.mul hq
lemma min_one (hq : RatBound q B) : RatBound (min 1 q) B := by
  by_cases h : 1≤q
  · rw [min_eq_left h]; exact one B hq.one_le
  · rw [min_eq_right (le_of_not_ge h)]; exact hq
lemma den_le (hq : RatBound q B) : q.den≤B := by
  obtain ⟨a,b,ha,hb,hpos,rfl⟩ := hq
  have he : ((a:ℚ)/(b:ℚ))=Rat.divInt (a:ℤ) (b:ℤ) := by simp [Rat.divInt_eq_div]
  rw [he]
  have hd := Rat.den_dvd (a:ℤ) (b:ℤ)
  exact (Nat.le_of_dvd hpos (Int.natCast_dvd_natCast.mp hd)).trans hb
end RatBound

section ActualSize
open scoped BigOperators Classical
lemma RatBound.nat_div (a b B : ℕ) (ha : a≤B) (hb : b≤B) (hB : 0<B) : RatBound ((a:ℚ)/b) B := by
  by_cases hz : b=0
  · subst b; simpa using RatBound.zero B hB
  · exact ⟨a,b,ha,hb,Nat.pos_of_ne_zero hz,rfl⟩
lemma indicator_list_sum {X : Type*} (P : X → Prop) (l : List X) :
    (l.map (fun x => if P x then (1:ℚ) else 0)).sum=(l.countP (fun x => decide (P x)):ℚ) := by
  induction l with
  | nil => simp
  | cons x l ih => by_cases hx : P x <;> simp [hx,ih,add_comm]
variable {Γ : Type*} [sectionInstance118 : Fintype Γ] [sectionInstance119 : DecidableEq Γ]
omit sectionInstance118 sectionInstance119 in
lemma rationalTypeRatio [Fintype Γ] [DecidableEq Γ] (gs : List (Γ × Γ)) (l : List (Set Γ)) (p r : Γ × Γ) :
    rationalEmpirical (rationalPlain gs (fun _ => 1)) l /
      rationalEmpirical (rationalDefect gs p r) l =
      (l.countP (fun S => decide (PlainState gs S)):ℚ)/
        (l.countP (fun S => decide (DefectState gs p r S)):ℚ) := by
  unfold rationalEmpirical rationalPlain rationalDefect
  rw [indicator_list_sum,indicator_list_sum]
  by_cases hz : l.length=0
  · have he : l=[] := List.length_eq_zero_iff.mp hz
    simp [he]
  · exact div_div_div_cancel_right₀ (by exact_mod_cast hz : (l.length:ℚ)≠0) _ _
lemma rationalLearn_bound (gs : List (Γ × Γ)) (w : (Γ × Γ) → (Γ × Γ) → ℚ)
    (l : List (Set Γ)) (B N : ℕ) (hN : 0<N) (hlen : l.length≤N)
    (hw : ∀ p r,RatBound (w p r) B) (p r : Γ × Γ) :
    RatBound (rationalLearn gs w l p r) (B*N) := by
  unfold rationalLearn
  split_ifs
  · apply (hw p r).mul
    rw [rationalTypeRatio]
    exact RatBound.nat_div _ _ N ((List.countP_le_length).trans hlen)
      ((List.countP_le_length).trans hlen) hN
  · exact (hw p r).mono (Nat.le_mul_of_pos_right _ hN)
lemma rationalHistory_bound {X : Type*} (gs : List (Γ × Γ)) (sample : X → List (Set Γ))
    (N : ℕ) (hN : 0<N) (hs : ∀ x,(sample x).length≤N) (h : List X) (p r : Γ × Γ) :
    RatBound (rationalHistory gs sample h p r) (4*N^h.length) := by
  induction h using List.reverseRecOn generalizing p r with
  | nil => simpa [rationalHistory] using RatBound.nat 4 4 (by omega) (by omega)
  | append_singleton h x ih =>
    have he : rationalHistory gs sample (h++[x])=rationalLearn gs (rationalHistory gs sample h) (sample x) := by
      funext p r; simp [rationalHistory,List.foldl_append]
    rw [he]
    have hh := rationalLearn_bound gs (rationalHistory gs sample h) (sample x) (4*N^h.length) N hN (hs x) ih p r
    simpa only [List.length_append,List.length_singleton,pow_succ,Nat.mul_assoc] using hh
omit sectionInstance119 in
lemma rationalMultiplier_bound [DecidableEq Γ] (gs : List (Γ × Γ)) (w : (Γ × Γ) → (Γ × Γ) → ℚ)
    (B : ℕ) (hB : 0<B) (hw : ∀ p r,RatBound (w p r) B) (S : Set Γ) :
    RatBound (rationalMultiplier gs w S) B := by
  unfold rationalMultiplier
  split_ifs
  · exact hw _ _
  · exact RatBound.one B hB
lemma rationalRho_bound (n : ℕ) (hn : 0<n) : RatBound (rationalRho n) (2*n) := by
  refine ⟨2*n-1,2*n,by omega,le_rfl,by omega,?_⟩
  have hnn : (n:ℚ)≠0 := by exact_mod_cast Nat.ne_of_gt hn
  have he : ((2*n-1:ℕ):ℚ)=2*(n:ℚ)-1 := by rw [Nat.cast_sub (by omega)]; push_cast; rfl
  rw [he,rationalRho]
  push_cast
  field_simp
omit sectionInstance118 sectionInstance119 in
lemma rationalAnneal_bound [Fintype Γ] [DecidableEq Γ] (M : Matroid Γ) (n j : ℕ) (hn : 0<n) (S : Set Γ) :
    RatBound (rationalAnneal M n j S) ((2*n)^(n*j)) := by
  have hh := ((rationalRho_bound n hn).pow j).pow (n-(M.eRk S).toNat)
  unfold rationalAnneal
  apply hh.mono
  rw [←pow_mul]
  apply Nat.pow_le_pow_right (by omega : 0<2*n)
  nlinarith [Nat.sub_le n (M.eRk S).toNat]
end ActualSize

section StoredSize
open scoped BigOperators Classical
variable (n N L : ℕ) (hN : 0<N)
include hN
lemma observedSets_length (x : PhaseSample n N) : (observedSets n N x).length=N := by
  rw [observedSets,List.length_map,FiniteChain.Sample.toList_length]
  omega
lemma rationalStored_bound (h : List (PhaseSample n N)) (hlen : h.length≤L) (j : ℕ) (p r) :
    RatBound (rationalStored n N h j p r) (4*N^L) := by
  have hd := rationalHistory_bound (pairedSlots n) (observedSets n N) N hN
    (fun x => (observedSets_length n N hN x).le) (h.take j) p r
  apply hd.mono
  apply Nat.mul_le_mul_left
  apply Nat.pow_le_pow_right hN
  rw [List.length_take]
  exact (Nat.min_le_right _ _).trans hlen
lemma rationalWeight_bound (hn : 0<n) (M : Matroid (Fin n ⊕ Fin n))
    (h : List (PhaseSample n N)) (hlen : h.length≤L) (j : ℕ) (hj : j≤L) (S : Set (Fin n ⊕ Fin n)) :
    RatBound (rationalWeight (pairedSlots n) (rationalStored n N h j) (rationalAnneal M n j) S)
      (4*N^L*(2*n)^(n*L)) := by
  unfold rationalWeight
  apply RatBound.mul
  · exact rationalMultiplier_bound _ _ _ (by positivity) (rationalStored_bound n N L hN h hlen j) S
  · apply (rationalAnneal_bound M n j hn S).mono
    apply Nat.pow_le_pow_right (by omega : 0<2*n)
    exact Nat.mul_le_mul_left n hj
lemma rationalAcceptance_bound (hn : 0<n) (M : Matroid (Fin n ⊕ Fin n))
    (h : List (PhaseSample n N)) (hlen : h.length≤L) (j : ℕ) (hj : j≤L)
    (S T : ChainIndex (pairedSlots n)) :
    RatBound (rationalAcceptance (pairedSlots n) (rationalStored n N h j) (rationalAnneal M n j) S T)
      ((4*N^L*(2*n)^(n*L))^2) := by
  unfold rationalAcceptance
  have ha := (rationalWeight_bound n N L hN hn M h hlen j hj T.val).div
    (rationalWeight_bound n N L hN hn M h hlen j hj S.val)
  simpa only [pow_two] using ha.min_one
end StoredSize

open scoped BigOperators Classical
lemma acceptance_word_bound (n N L : ℕ) :
    (4*N^L*(2*n)^(n*L))^2 ≤ 2^(drawWordBound n N L) := by
  have hN := Nat.pow_le_pow_left (Nat.lt_two_pow_self (n:=N)).le L
  have hn := Nat.pow_le_pow_left (Nat.lt_two_pow_self (n:=2*n)).le (n*L)
  have hw : 4*N^L*(2*n)^(n*L)≤2^(2+N*L+(2*n)*(n*L)) := by
    calc
      _ ≤ 4*(2^N)^L*(2^(2*n))^(n*L) := Nat.mul_le_mul (Nat.mul_le_mul_left 4 hN) hn
      _ = _ := by rw [←pow_mul,←pow_mul]; rw [show (4:ℕ)=2^2 by norm_num,←pow_add,←pow_add]
  calc
    _ ≤ (2^(2+N*L+(2*n)*(n*L)))^2 := Nat.pow_le_pow_left hw 2
    _ = 2^(2*(2+N*L+(2*n)*(n*L))) := by rw [←pow_mul]; congr 1; omega
    _ ≤ _ := Nat.pow_le_pow_right (by omega) (by unfold drawWordBound; omega)
lemma drawWordBound_ge_one (n N L : ℕ) : 1≤drawWordBound n N L := by unfold drawWordBound; omega
lemma drawWordBound_ge_n (n N L : ℕ) : n≤drawWordBound n N L := by unfold drawWordBound; omega
lemma drawWordBound_exchange (n N L : ℕ) : Nat.clog 2 (n^2)≤drawWordBound n N L := by
  apply Nat.clog_le_of_le_pow
  exact (Nat.lt_two_pow_self (n:=n^2)).le.trans (Nat.pow_le_pow_right (by omega) (by unfold drawWordBound; omega))

section ActualFits
open scoped BigOperators Classical
variable (n : ℕ) (hn : 0<n) (M : Matroid (Fin n ⊕ Fin n)) (N L : ℕ) (hN : 0<N)
local notation "GS" => pairedSlots n
local notation "H" => drawWordBound n N L
include hN in
lemma actualStepTree_fits (h : List (PhaseSample n N)) (hlen : h.length≤L) (j : ℕ) (hj : j≤L)
    (x : ChainIndex GS) : DrawTree.Fits H 3 (actualStepTree n hn M N h j x) := by
  let : Nonempty (ExchangeChoice x.val) := Fintype.card_pos_iff.mp (by
    rw [exchangeChoice_card GS (pairedSlots_fresh n) (pairedSlots_cover n),pairedSlots_length]; positivity)
  unfold actualStepTree rationalMetropolis
  apply DrawTree.fits_bind H 1 2 _ _
  · apply DrawTree.bernoulli_fits
    norm_num
    exact drawWordBound_ge_one n N L
  · intro lazy
    cases lazy with
    | true => trivial
    | false =>
      simp only [Bool.false_eq_true,ite_false]
      apply DrawTree.fits_bind H 1 1 _ _
      · apply DrawTree.uniformChoice_fits
        rw [exchangeChoice_card GS (pairedSlots_fresh n) (pairedSlots_cover n),pairedSlots_length]
        exact drawWordBound_exchange n N L
      · intro a
        unfold rationalExchange
        split_ifs
        · apply DrawTree.map_fits
          apply DrawTree.bernoulli_fits
          apply Nat.clog_le_of_le_pow
          exact (rationalAcceptance_bound n N L hN hn M h hlen j hj x _).den_le.trans
            (acceptance_word_bound n N L)
        · trivial
include hN in
lemma actualTraceTree_fits (h : List (PhaseSample n N)) (hlen : h.length≤L) (j cap : ℕ) (hj : j≤L)
    (x : PlainIndex GS) : DrawTree.Fits H (3*(cap+1)) (actualTraceTree n hn M N h j cap x) := by
  exact hittingTree_fits _ _ H 3 (cap+1) (actualStepTree_fits n hn M N L hN h hlen j hj) x.val
include hN in
lemma actualRestartTree_fits (h : List (PhaseSample n N)) (hlen : h.length≤L) (cap j : ℕ) (hj : j≤L) :
    DrawTree.Fits H (1+3*j*(cap+1)*(20*n^4*(n*(L+1)+2))) (actualRestartTree n hn M N L h cap j) := by
  let := plainIndex_nonempty GS (pairedSlots_fresh n) (pairedSlots_cover n)
  induction j with
  | zero =>
    rw [actualRestartTree]
    simp only [Nat.mul_zero,Nat.zero_mul,Nat.add_zero]
    apply DrawTree.map_fits
    apply DrawTree.uniformChoice_fits
    rw [plainIndex_card,Nat.clog_pow 2 n (by omega)]
    exact drawWordBound_ge_n n N L
  | succ j ih =>
    rw [actualRestartTree]
    have hh := DrawTree.optionBind_fits (actualRestartTree n hn M N L h cap j)
      (DrawTree.iterate (actualTraceTree n hn M N h (j+1) cap) (20*n^4*(n*(L+1)+2))) H
      (1+3*j*(cap+1)*(20*n^4*(n*(L+1)+2))) (3*(cap+1)*(20*n^4*(n*(L+1)+2)))
      (ih (by omega))
      (DrawTree.iterate_fits _ H (3*(cap+1)) _ (actualTraceTree_fits n hn M N L hN h hlen (j+1) cap hj))
    convert hh using 1 <;> first | rfl | ring

include hN in
lemma actualPhaseTree_fits (h : List (PhaseSample n N)) (hlen : h.length≤L) :
    DrawTree.Fits H (phaseDrawBound n N L) (actualPhaseTree n hn M N L h) := by
  unfold actualPhaseTree
  split_ifs
  · have hstart : DrawTree.Fits H (1+3*L*(restartCap n L+1)*(20*n^4*(n*(L+1)+2))) (actualStartTree n hn M N L h) := by
      apply DrawTree.map_fits
      apply DrawTree.fits_mono_steps H _ _ _ _
        (actualRestartTree_fits n hn M N L hN h hlen (restartCap n L) h.length hlen)
      gcongr
    apply DrawTree.optionBind_fits _ _ H _ (3*N) hstart
    intro x
    apply DrawTree.map_fits
    apply DrawTree.fits_mono_steps H (3*(N-1)) (3*N) (by omega)
    exact DrawTree.sample_fits _ H 3 (N-1) (actualStepTree_fits n hn M N L hN h hlen h.length hlen) x
  · cases phaseDrawBound n N L <;> trivial
end ActualFits

namespace DrawTree
variable {A B C : Type*}
lemma bind_assoc (t : DrawTree A) (f : A → DrawTree B) (g : B → DrawTree C) :
    (t.bind f).bind g=t.bind (fun a => (f a).bind g) := by
  induction t with
  | leaf a => rfl
  | draw v k ih => simp only [bind,ih]
lemma optionBind_assoc (t : DrawTree (Option A)) (f : A → DrawTree (Option B)) (g : B → DrawTree (Option C)) :
    (t.optionBind f).optionBind g=t.optionBind (fun a => (f a).optionBind g) := by
  simp only [optionBind,bind_assoc]
  congr 1; funext a; cases a <;> rfl
lemma leaf_fits (H M : ℕ) (a : A) : Fits H M (.leaf a) := by cases M <;> trivial
end DrawTree
section AlgorithmFits
open scoped BigOperators Classical
variable (n : ℕ) (hn : 0<n) (M₁ M₂ : Matroid (Fin n)) (N L : ℕ) (hN : 0<N)
local notation "K" => pairedMatroid M₁ M₂
local notation "H" => drawWordBound n N L
local notation "B" => phaseDrawBound n N L
include hN in
lemma rationalWitnessTree_fits (h : List (PhaseSample n N)) (hlen : h.length≤L) :
    DrawTree.Fits H B (rationalWitnessTree n hn M₁ M₂ N L h) := by
  unfold rationalWitnessTree
  split_ifs
  · apply DrawTree.fits_mono_steps H _ B _ _
      (actualRestartTree_fits n hn K N L hN h hlen (restartCap n L) h.length hlen)
    unfold phaseDrawBound
    have hh : 3*h.length*(restartCap n L+1)*(20*n^4*(n*(L+1)+2))≤
        3*L*(restartCap n L+1)*(20*n^4*(n*(L+1)+2)) := by gcongr
    omega
  · exact DrawTree.leaf_fits H B none
include hN in
lemma rational_history_finish_fits (h : List (PhaseSample n N)) (k : ℕ) (hlen : h.length+k≤L) :
    DrawTree.Fits H (B*(k+1))
      ((DrawTree.history (actualPhaseTree n hn K N L) k h).optionBind (fun h =>
        (rationalWitnessTree n hn M₁ M₂ N L h).map (Option.map (rationalGuard n M₁ M₂ N L h)))) := by
  induction k generalizing h with
  | zero =>
    simp only [DrawTree.history,DrawTree.pureSome,DrawTree.optionBind,DrawTree.bind,Nat.zero_add,Nat.mul_one]
    exact DrawTree.map_fits _ _ H B (rationalWitnessTree_fits n hn M₁ M₂ N L hN h (by omega))
  | succ k ih =>
    rw [DrawTree.history,DrawTree.optionBind_assoc]
    have hh := DrawTree.optionBind_fits
      (actualPhaseTree n hn K N L h)
      (fun x => (DrawTree.history (actualPhaseTree n hn K N L) k (h++[x])).optionBind (fun h =>
        (rationalWitnessTree n hn M₁ M₂ N L h).map (Option.map (rationalGuard n M₁ M₂ N L h))))
      H B (B*(k+1)) (actualPhaseTree_fits n hn K N L hN h (by omega)) (by
        intro x; apply ih; simp only [List.length_append,List.length_singleton]; omega)
    convert hh using 1 <;> first | rfl | ring
include hN in
lemma rationalAlgorithmTree_fits : DrawTree.Fits H (algorithmDrawBound n N L) (rationalAlgorithmTree n hn M₁ M₂ N L) :=
  rational_history_finish_fits n hn M₁ M₂ N L hN [] L (by simp)
end AlgorithmFits

namespace DrawTree
variable {A B : Type*}
lemma all_bind (t : DrawTree A) (f : A → DrawTree B) (p : B → Prop)
    (hf : ∀ a,All p (f a)) : All p (t.bind f) := by
  induction t with
  | leaf a => exact hf a
  | draw v k ih => exact ih
lemma all_map (t : DrawTree A) (f : A → B) (p : B → Prop) (hf : ∀ a,p (f a)) : All p (t.map f) :=
  all_bind t _ p hf
lemma run_all (H D M : ℕ) (t : DrawTree A) (p : A → Prop) (ht : All p t) (bits) (a : A)
    (ha : run H D M t bits=some a) : p a := by
  induction M generalizing t with
  | zero =>
    cases t with
    | leaf x => simp only [run,Option.some.injEq] at ha; exact ha ▸ ht
    | draw v k => simp [run] at ha
  | succ M ih =>
    cases t with
    | leaf x => simp only [run,Option.some.injEq] at ha; exact ha ▸ ht
    | draw v k =>
      simp only [run] at ha
      split_ifs at ha with h
      · split at ha
        · simp at ha
        · exact ih _ (ht _) _ ha
end DrawTree
section AlgorithmAll
open scoped Classical
variable (n : ℕ) (hn : 0<n) (M₁ M₂ : Matroid (Fin n)) (N L : ℕ)
include hn in
lemma rationalAlgorithmTree_all : DrawTree.All
    (fun a : Option ℚ => ∀ z,a=some z → 0≤z ∧
      (M₂.E=Set.univ → M₁.eRank=M₂.eRank → commonBaseCount M₁ M₂=0 → z=0))
    (rationalAlgorithmTree n hn M₁ M₂ N L) := by
  unfold rationalAlgorithmTree DrawTree.optionBind
  apply DrawTree.all_bind
  intro a
  cases a with
  | none => intro z; simp
  | some h =>
    apply DrawTree.all_map
    intro a
    cases a with
    | none => intro z; simp
    | some x =>
      intro z hz
      simp only [Option.map_some,Option.some.injEq] at hz
      subst z
      exact ⟨rationalGuard_nonneg n hn M₁ M₂ N L h x,
        fun hE hr hZ => rationalGuard_zero n M₁ M₂ N L hE hr hZ h x⟩
end AlgorithmAll
open scoped BigOperators Classical
lemma uniformAverage_one_sub {X : Type*} [Fintype X] [Nonempty X] (f : X → ℝ) :
    uniformAverage (fun x => 1-f x)=1-uniformAverage f := by
  unfold uniformAverage
  simp only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
  rw [sub_div,div_self (by exact_mod_cast ne_of_gt (Fintype.card_pos))]
lemma rejectionBudget (M : ℕ) : (M:ℝ)*(1/2:ℝ)^(M+6)≤1/64 := by
  have hM : (M:ℝ)≤(2:ℝ)^M := by exact_mod_cast (Nat.lt_two_pow_self (n:=M)).le
  have h := mul_le_mul_of_nonneg_right hM (by positivity : 0≤(1/2:ℝ)^(M+6))
  apply h.trans
  rw [pow_add,←mul_assoc,←mul_pow]
  norm_num
lemma fairOutput_nonneg (n : ℕ) (hn : 0<n) (M₁ M₂ : Matroid (Fin n)) (N L : ℕ) (bits : FairBank n N L) :
    0≤fairOutput n hn M₁ M₂ N L bits := by
  unfold fairOutput
  generalize he : DrawTree.run _ _ _ _ bits=a
  cases a with
  | none => simp
  | some a =>
    cases a with
    | none => simp
    | some z =>
      simp only [Option.join_some,Option.getD_some]
      exact (DrawTree.run_all _ _ _ _ _ (rationalAlgorithmTree_all n hn M₁ M₂ N L) bits (some z) he z rfl).1
lemma fairOutput_zero (n : ℕ) (hn : 0<n) (M₁ M₂ : Matroid (Fin n)) (N L : ℕ)
    (hE₂ : M₂.E=Set.univ) (hr : M₁.eRank=M₂.eRank) (hZ : commonBaseCount M₁ M₂=0) (bits : FairBank n N L) :
    fairOutput n hn M₁ M₂ N L bits=0 := by
  unfold fairOutput
  generalize he : DrawTree.run _ _ _ _ bits=a
  cases a with
  | none => simp
  | some a =>
    cases a with
    | none => simp
    | some z =>
      simp only [Option.join_some,Option.getD_some]
      exact (DrawTree.run_all _ _ _ _ _ (rationalAlgorithmTree_all n hn M₁ M₂ N L) bits (some z) he z rfl).2 hE₂ hr hZ

theorem fair_single_success (n : ℕ) (hn : 0<n) (M₁ M₂ : Matroid (Fin n)) (N : ℕ)
    (hE₁ : M₁.E=Set.univ) (hE₂ : M₂.E=Set.univ) (hr : M₁.eRank=M₂.eRank)
    (ε : ℚ) (hε0 : 0<ε) (hε1 : ε<1) (b : ℕ) (hb : (1/2:ℝ)^b ≤ (ε:ℝ)/10)
    (hN : (10:ℝ)^10*(annealLength n b+1)*n^14/(annealTolerance (ε:ℝ) (annealLength n b))^2 ≤ N) :
    11/16 ≤ uniformAverage (fun bits : FairBank n N (annealLength n b) =>
      if relativeAccuracy ε (commonBaseCount M₁ M₂) (fairOutput n hn M₁ M₂ N (annealLength n b) bits) then (1:ℝ) else 0) := by
  by_cases hZ : commonBaseCount M₁ M₂=0
  · simp only [fairOutput_zero n hn M₁ M₂ N _ hE₂ hr hZ,hZ,relativeAccuracy,Nat.cast_zero,mul_zero,le_refl,and_self,ite_true,uniformAverage_const]
    norm_num
  have hN0 : 0<N := by
    have h : 0<(10:ℝ)^10*(annealLength n b+1)*n^14/(annealTolerance (ε:ℝ) (annealLength n b))^2 := by
      have hε : (0:ℝ)<ε := by exact_mod_cast hε0
      have hn' : (0:ℝ)<n := by exact_mod_cast hn
      unfold annealTolerance
      positivity
    exact_mod_cast lt_of_lt_of_le h hN
  let L := annealLength n b
  let φ : ℚ → ℝ := fun z => if relativeAccuracy ε (commonBaseCount M₁ M₂) z then 1 else 0
  have hs := rational_algorithm_success n hn M₁ M₂ N hE₁ hE₂ hr ε hε0 hε1 b hb (Nat.pos_of_ne_zero hZ) hN
  have hrun := DrawTree.run_lower (drawWordBound n N L) (algorithmDrawBound n N L+6) (algorithmDrawBound n N L)
    (rationalAlgorithmTree n hn M₁ M₂ N L) (rationalAlgorithmTree_fits n hn M₁ M₂ N L hN0)
    (DrawTree.optionValue φ) (by intro a; cases a with
      | none => norm_num [DrawTree.optionValue]
      | some z => dsimp [DrawTree.optionValue,φ]; split_ifs <;> norm_num)
    (by intro a; cases a with
      | none => norm_num [DrawTree.optionValue]
      | some z => dsimp [DrawTree.optionValue,φ]; split_ifs <;> norm_num)
  have hm : uniformAverage (fun bits : FairBank n N L => DrawTree.optionValue (DrawTree.optionValue φ)
      (DrawTree.run (drawWordBound n N L) (algorithmDrawBound n N L+6) (algorithmDrawBound n N L)
        (rationalAlgorithmTree n hn M₁ M₂ N L) bits)) ≤
      uniformAverage (fun bits : FairBank n N L => φ (fairOutput n hn M₁ M₂ N L bits)) := by
    apply uniformAverage_mono
    intro bits
    unfold fairOutput
    generalize DrawTree.run _ _ _ _ bits=a
    cases a with
    | none => dsimp [DrawTree.optionValue,φ]; split_ifs <;> norm_num
    | some a => cases a <;> dsimp [DrawTree.optionValue,φ] <;> split_ifs <;> norm_num
  have hbudget := rejectionBudget (algorithmDrawBound n N L)
  change 11/16≤uniformAverage (fun bits : FairBank n N L => φ (fairOutput n hn M₁ M₂ N L bits))
  change 3/4≤(rationalAlgorithmTree n hn M₁ M₂ N L).expectation (DrawTree.optionValue φ) at hs
  linarith
open scoped BigOperators Classical

lemma median_bad_count (l : List ℚ) (hl : 0<l.length) (a b : ℚ)
    (hbad : ¬(a≤rationalMedian l ∧ rationalMedian l≤b)) :
    l.length ≤ 2*l.countP (outsideInterval a b) := by
  let s := l.mergeSort (· ≤ ·)
  have hlen : s.length=l.length := List.length_mergeSort _
  have hs : s.SortedLE := List.sortedLE_mergeSort
  have hk : l.length/2<s.length := by rw [hlen]; omega
  have he : rationalMedian l=s[l.length/2] := List.getD_eq_getElem s 0 hk
  rw [he] at hbad
  have hc : s.countP (outsideInterval a b)=l.countP (outsideInterval a b) :=
    List.Perm.countP_eq _ (List.mergeSort_perm _ _)
  by_cases ha : a ≤ s[l.length/2]
  · have hb : b < s[l.length/2] := lt_of_not_ge (fun hh => hbad ⟨ha,hh⟩)
    have htail : (s.drop (l.length/2)).countP (outsideInterval a b)=(s.drop (l.length/2)).length := by
      apply List.countP_eq_length.mpr
      intro x hx
      obtain ⟨i,hi,rfl⟩ := List.getElem_of_mem hx
      rw [List.getElem_drop]
      apply decide_eq_true
      intro hh
      have hm := hs.getElem_le_getElem_of_le (i := l.length/2) (j := l.length/2+i) (hi := hk) (hj := by simp only [List.length_drop] at hi; omega) (by omega)
      exact (not_le_of_gt (hb.trans_le hm)) hh.2
    have hdecomp := List.countP_append (p := outsideInterval a b)
      (l₁ := s.take (l.length/2)) (l₂ := s.drop (l.length/2))
    rw [List.take_append_drop,htail,hc,List.length_drop,hlen] at hdecomp
    omega
  · have hfront : (s.take (l.length/2+1)).countP (outsideInterval a b)=(s.take (l.length/2+1)).length := by
      apply List.countP_eq_length.mpr
      intro x hx
      obtain ⟨i,hi,rfl⟩ := List.getElem_of_mem hx
      rw [List.getElem_take]
      apply decide_eq_true
      intro hh
      have hi' : i≤l.length/2 := by simp only [List.length_take] at hi; omega
      have hm := hs.getElem_le_getElem_of_le (i := i) (j := l.length/2) (hi := by simp only [List.length_take] at hi; omega) (hj := hk) hi'
      exact ha (hh.1.trans hm)
    have hdecomp := List.countP_append (p := outsideInterval a b)
      (l₁ := s.take (l.length/2+1)) (l₂ := s.drop (l.length/2+1))
    rw [List.take_append_drop,hfront,hc,List.length_take,hlen] at hdecomp
    omega

lemma uniformAverage_mul_const {X : Type*} [Fintype X] (f : X → ℝ) (c : ℝ) :
    uniformAverage (fun x => f x*c)=uniformAverage f*c := by
  unfold uniformAverage
  rw [← Finset.sum_mul]
  ring

lemma countP_ofFn_cons {X : Type*} (p : X → Bool) (x : X) {R : ℕ} (xs : Fin R → X) :
    (List.ofFn (Fin.cons x xs)).countP p=(if p x then 1 else 0)+(List.ofFn xs).countP p := by
  rw [List.ofFn_succ]
  simp only [Fin.cons_zero,Fin.cons_succ,List.countP_cons]
  change (List.ofFn xs).countP p+(if p x then 1 else 0)=(if p x then 1 else 0)+(List.ofFn xs).countP p
  omega

lemma independent_bad_moment {X : Type*} [Fintype X] [Nonempty X]
    (bad : X → Bool) (R : ℕ) :
    uniformAverage (fun xs : Fin R → X => (4:ℝ)^((List.ofFn xs).countP bad))=
      (1+3*uniformAverage (fun x => if bad x then (1:ℝ) else 0))^R := by
  induction R with
  | zero => simp [List.ofFn_zero,uniformAverage_const]
  | succ R ih =>
    rw [uniformAverage_fin_succ]
    simp_rw [countP_ofFn_cons,pow_add,uniformAverage_mul_left,ih]
    rw [uniformAverage_mul_const]
    have he : (fun x : X => (4:ℝ)^(if bad x then 1 else 0:ℕ))=
        fun x => 1+3*(if bad x then (1:ℝ) else 0) := by
      funext x; cases bad x <;> norm_num
    rw [he,uniformAverage_add,uniformAverage_const,uniformAverage_mul_left,pow_succ]
    ring

lemma countP_map {X Y : Type*} (l : List X) (f : X → Y) (p : Y → Bool) :
    (l.map f).countP p=l.countP (fun x => p (f x)) := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons,List.countP_cons,ih]

theorem median_failure_bound {X : Type*} [Fintype X] [Nonempty X]
    (output : X → ℚ) (a b : ℚ) (R : ℕ) (hR : 0<R)
    (hbad : uniformAverage (fun x => if outsideInterval a b (output x) then (1:ℝ) else 0)≤5/16) :
    uniformAverage (fun xs : Fin R → X =>
      if outsideInterval a b (rationalMedian (List.ofFn (fun i => output (xs i))))
      then (1:ℝ) else 0) ≤ (31/32:ℝ)^R := by
  let bad : X → Bool := fun x => outsideInterval a b (output x)
  have hx : ∀ xs : Fin R → X,
      (if outsideInterval a b (rationalMedian (List.ofFn (fun i => output (xs i)))) then (1:ℝ) else 0)
      ≤ (4:ℝ)^((List.ofFn xs).countP bad)/(2:ℝ)^R := by
    intro xs
    by_cases he : outsideInterval a b (rationalMedian (List.ofFn (fun i => output (xs i))))=true
    · rw [ite_eq_left he]
      have hc := median_bad_count (List.ofFn (fun i => output (xs i))) (by simpa using hR) a b (by
        simpa only [outsideInterval,decide_eq_true_eq] using he)
      have hmap : List.ofFn (fun i => output (xs i))=(List.ofFn xs).map output := by rw [List.map_ofFn]; rfl
      rw [hmap,countP_map,List.length_map,List.length_ofFn] at hc
      have hp : (2:ℝ)^R≤4^((List.ofFn xs).countP bad) := by
        calc
          (2:ℝ)^R ≤ 2^(2*((List.ofFn xs).countP bad)) := pow_le_pow_right₀ (by norm_num) hc
          _ = _ := by rw [pow_mul]; norm_num
      exact (le_div_iff₀ (by positivity)).mpr (by simpa using hp)
    · rw [ite_eq_right he]; positivity
  have hm := uniformAverage_mono _ _ hx
  have hrw : uniformAverage (fun xs : Fin R → X => (4:ℝ)^((List.ofFn xs).countP bad)/(2:ℝ)^R)=
      (1+3*uniformAverage (fun x => if bad x then (1:ℝ) else 0))^R/(2:ℝ)^R := by
    simp_rw [div_eq_mul_inv]
    rw [uniformAverage_mul_const,independent_bad_moment]
  rw [hrw] at hm
  apply hm.trans
  rw [←div_pow]
  apply pow_le_pow_left₀ (by
    apply div_nonneg _ (by norm_num)
    have hz := uniformAverage_nonneg (fun x => if bad x then (1:ℝ) else 0) (by intro x; split_ifs <;> norm_num)
    linarith)
  dsimp [bad] at *
  linarith

lemma repetitionCount_pos (δ : ℚ) : 0<repetitionCount δ := by unfold repetitionCount; omega
lemma rational_binary_accuracy (δ : ℚ) (hδ : 0<δ) :
    (1/2:ℝ)^(δ.den.bits.length+1) ≤ (δ:ℝ) := by
  have hd : (0:ℝ)<δ.den := by exact_mod_cast δ.den_pos
  have hn : (1:ℝ)≤(δ.num:ℝ) := by exact_mod_cast (show (1:ℤ)≤δ.num by have h := Rat.num_pos.mpr hδ; omega)
  have hp : (δ.den:ℝ)≤(2:ℝ)^(δ.den.bits.length+1) := by
    exact_mod_cast (Nat.le_of_lt ((Nat.size_le.mp (show δ.den.size≤δ.den.bits.length+1 by rw [Nat.size_eq_bits_len]; omega))))
  rw [one_div,inv_pow,Rat.cast_def]
  apply le_trans (inv_anti₀ hd hp)
  rw [inv_eq_one_div]
  exact div_le_div_of_nonneg_right hn hd.le
lemma confidence_decay (δ : ℚ) (hδ : 0<δ) :
    (31/32:ℝ)^(repetitionCount δ) ≤ (δ:ℝ) := by
  unfold repetitionCount
  rw [pow_mul]
  apply le_trans _ (rational_binary_accuracy δ hδ)
  apply pow_le_pow_left₀ (by positivity)
  norm_num

theorem median_confidence {X : Type*} [Fintype X] [Nonempty X]
    (output : X → ℚ) (a b : ℚ) (δ : ℚ) (hδ : 0<δ)
    (hbad : uniformAverage (fun x => if outsideInterval a b (output x) then (1:ℝ) else 0)≤5/16) :
    1-(δ:ℝ) ≤ uniformAverage (fun xs : Fin (repetitionCount δ) → X =>
      if a≤rationalMedian (List.ofFn (fun i => output (xs i))) ∧
        rationalMedian (List.ofFn (fun i => output (xs i)))≤b then (1:ℝ) else 0) := by
  have h := (median_failure_bound output a b (repetitionCount δ) (repetitionCount_pos δ) hbad).trans
    (confidence_decay δ hδ)
  have he : (fun xs : Fin (repetitionCount δ) → X =>
      if outsideInterval a b (rationalMedian (List.ofFn (fun i => output (xs i)))) then (1:ℝ) else 0)=
    fun xs => 1-(if a≤rationalMedian (List.ofFn (fun i => output (xs i))) ∧
        rationalMedian (List.ofFn (fun i => output (xs i)))≤b then (1:ℝ) else 0) := by
    funext xs
    simp only [outsideInterval,decide_eq_true_eq]
    split_ifs <;> simp_all
  rw [he] at h
  have hei : uniformAverage (fun xs : Fin (repetitionCount δ) → X =>
      1-(if a≤rationalMedian (List.ofFn (fun i => output (xs i))) ∧
        rationalMedian (List.ofFn (fun i => output (xs i)))≤b then (1:ℝ) else 0))=
      1-uniformAverage (fun xs : Fin (repetitionCount δ) → X =>
      if a≤rationalMedian (List.ofFn (fun i => output (xs i))) ∧
        rationalMedian (List.ofFn (fun i => output (xs i)))≤b then (1:ℝ) else 0) := by
    unfold uniformAverage
    simp only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
    rw [sub_div,div_self (by exact_mod_cast ne_of_gt (Fintype.card_pos))]
  rw [hei] at h
  linarith

open scoped BigOperators Classical
lemma rationalMedian_all (p : ℚ → Prop) (l : List ℚ) (h0 : p 0) (hl : ∀ z∈l,p z) : p (rationalMedian l) := by
  unfold rationalMedian
  by_cases h : l.length/2<(l.mergeSort (· ≤ ·)).length
  · rw [List.getD_eq_getElem _ _ h]
    apply hl
    exact (List.mem_mergeSort).mp (List.getElem_mem h)
  · have hl0 : l.length=0 := by simp only [List.length_mergeSort] at h; omega
    have he : l=[] := List.length_eq_zero_iff.mp hl0
    simpa [he] using h0

lemma accuracyExponent_spec (ε : ℚ) (hε : 0<ε) : (1/2:ℝ)^(accuracyExponent ε)≤(ε:ℝ)/10 := by
  have h := rational_binary_accuracy ε hε
  have he : (0:ℝ)<ε := by exact_mod_cast hε
  unfold accuracyExponent
  rw [show ε.den.bits.length+5=(ε.den.bits.length+1)+4 by omega,pow_add]
  norm_num
  nlinarith

lemma sampleCount_spec (n L : ℕ) (ε : ℚ) (hε : 0<ε) :
    (10:ℝ)^10*(L+1)*n^14/(annealTolerance (ε:ℝ) L)^2≤ sampleCount n L ε := by
  have hε' : (0:ℝ)<ε := by exact_mod_cast hε
  have hi : (ε:ℝ)⁻¹≤(⌈ε⁻¹⌉₊:ℝ) := by exact_mod_cast Nat.le_ceil (ε⁻¹)
  have hex : (10:ℝ)^10*(L+1)*n^14/(annealTolerance (ε:ℝ) L)^2=
      (1024*10^10:ℝ)*(L+1)^3*n^14*((ε:ℝ)⁻¹)^2 := by
    unfold annealTolerance
    field_simp
    ; ring
  rw [hex]
  calc
    _ ≤ (10:ℝ)^14*(L+1)^3*n^14*(⌈ε⁻¹⌉₊:ℝ)^2 := by
      gcongr
      norm_num
    _ ≤ _ := by unfold sampleCount; push_cast; linarith

lemma amplifiedOutput_nonneg (n : ℕ) (hn : 0<n) (M₁ M₂ : Matroid (Fin n)) (N L : ℕ) (δ : ℚ) (bits) :
    0≤amplifiedOutput n hn M₁ M₂ N L δ bits := by
  apply rationalMedian_all (fun z => 0≤z) _ (by norm_num)
  intro z hz
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hz
  exact fairOutput_nonneg n hn M₁ M₂ N L (bits i)
lemma amplifiedOutput_zero (n : ℕ) (hn : 0<n) (M₁ M₂ : Matroid (Fin n)) (N L : ℕ) (δ : ℚ)
    (hE₂ : M₂.E=Set.univ) (hr : M₁.eRank=M₂.eRank) (hZ : commonBaseCount M₁ M₂=0) (bits) :
    amplifiedOutput n hn M₁ M₂ N L δ bits=0 := by
  apply rationalMedian_all (fun z => z=0) _ rfl
  intro z hz
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hz
  exact fairOutput_zero n hn M₁ M₂ N L hE₂ hr hZ (bits i)

theorem amplified_success (n : ℕ) (hn : 0<n) (M₁ M₂ : Matroid (Fin n)) (N : ℕ)
    (hE₁ : M₁.E=Set.univ) (hE₂ : M₂.E=Set.univ) (hr : M₁.eRank=M₂.eRank)
    (ε δ : ℚ) (hε0 : 0<ε) (hε1 : ε<1) (hδ : 0<δ)
    (b : ℕ) (hb : (1/2:ℝ)^b≤(ε:ℝ)/10)
    (hN : (10:ℝ)^10*(annealLength n b+1)*n^14/(annealTolerance (ε:ℝ) (annealLength n b))^2≤N) :
    1-(δ:ℝ)≤uniformAverage (fun bits : Fin (repetitionCount δ) → FairBank n N (annealLength n b) =>
      if relativeAccuracy ε (commonBaseCount M₁ M₂) (amplifiedOutput n hn M₁ M₂ N (annealLength n b) δ bits)
        then (1:ℝ) else 0) := by
  have hbad : uniformAverage (fun bits : FairBank n N (annealLength n b) =>
      if outsideInterval ((1-ε)*(commonBaseCount M₁ M₂:ℚ)) ((1+ε)*(commonBaseCount M₁ M₂:ℚ))
        (fairOutput n hn M₁ M₂ N (annealLength n b) bits) then (1:ℝ) else 0)≤5/16 := by
    have hs := fair_single_success n hn M₁ M₂ N hE₁ hE₂ hr ε hε0 hε1 b hb hN
    have he : (fun bits : FairBank n N (annealLength n b) =>
        if outsideInterval ((1-ε)*(commonBaseCount M₁ M₂:ℚ)) ((1+ε)*(commonBaseCount M₁ M₂:ℚ))
          (fairOutput n hn M₁ M₂ N (annealLength n b) bits) then (1:ℝ) else 0)=
        fun bits => 1-(if relativeAccuracy ε (commonBaseCount M₁ M₂)
          (fairOutput n hn M₁ M₂ N (annealLength n b) bits) then (1:ℝ) else 0) := by
      funext bits
      by_cases hh : relativeAccuracy ε (commonBaseCount M₁ M₂)
          (fairOutput n hn M₁ M₂ N (annealLength n b) bits)
      · simp only [hh,ite_true,sub_self]
        simp only [relativeAccuracy] at hh
        simp [outsideInterval,hh]
      · simp only [hh,ite_false,sub_zero]
        simp only [relativeAccuracy] at hh
        simp [outsideInterval,hh]
    rw [he,uniformAverage_one_sub]
    linarith
  have hm := median_confidence (fairOutput n hn M₁ M₂ N (annealLength n b))
    ((1-ε)*(commonBaseCount M₁ M₂:ℚ)) ((1+ε)*(commonBaseCount M₁ M₂:ℚ)) δ hδ hbad
  convert hm using 1
  congr 1
  funext bits
  unfold relativeAccuracy amplifiedOutput
  split_ifs <;> rfl

theorem bounded_fair_experiment (n : ℕ) (hn : 0<n) (M₁ M₂ : Matroid (Fin n))
    (hE₁ : M₁.E=Set.univ) (hE₂ : M₂.E=Set.univ) (hr : M₁.eRank=M₂.eRank)
    (ε δ : ℚ) (hε0 : 0<ε) (hε1 : ε<1) (hδ : 0<δ) :
    (∀ bits : FPRASBank n ε δ,0≤boundedFPRASOutput n hn M₁ M₂ ε δ bits ∧
      (commonBaseCount M₁ M₂=0 → boundedFPRASOutput n hn M₁ M₂ ε δ bits=0)) ∧
    1-(δ:ℝ)≤uniformAverage (fun bits : FPRASBank n ε δ =>
      if relativeAccuracy ε (commonBaseCount M₁ M₂) (boundedFPRASOutput n hn M₁ M₂ ε δ bits) then (1:ℝ) else 0) := by
  constructor
  · intro bits
    exact ⟨amplifiedOutput_nonneg n hn M₁ M₂ _ _ δ bits,
      fun hZ => amplifiedOutput_zero n hn M₁ M₂ _ _ δ hE₂ hr hZ bits⟩
  · exact amplified_success n hn M₁ M₂ _ hE₁ hE₂ hr ε δ hε0 hε1 hδ
      (accuracyExponent ε) (accuracyExponent_spec ε hε0)
      (sampleCount_spec n _ ε hε0)

section GreedyOracle
variable {α : Type*} [sectionInstance120 : DecidableEq α]

lemma greedyOracle_correct (M : Matroid α) (O : Finset α → Bool)
    (hO : ∀ I,O I = true ↔ M.Indep (I : Set α)) (l : List α)
    (hE : ∀ a ∈ l,a ∈ M.E) : M.IsBasis (greedyOracle O l : Set α) (l.toFinset : Set α) := by
  induction l with
  | nil => simp [greedyOracle]
  | cons a l ih =>
    have hi := ih (fun x hx => hE x (by simp [hx]))
    have ha := hE a (by simp)
    simp only [greedyOracle]
    split_ifs with h
    · have hind := (hO _).mp h
      apply hind.isBasis_of_subset_of_subset_closure
      · simpa only [List.toFinset_cons,Finset.coe_insert] using Set.insert_subset_insert hi.subset
      · simp only [List.toFinset_cons,Finset.coe_insert]
        apply Set.insert_subset
        · simpa only [Finset.coe_insert] using M.subset_closure _ hind.subset_ground (Finset.mem_insert_self a _)
        · exact hi.subset_closure.trans (M.closure_mono (by simp))
    · apply hi.indep.isBasis_of_subset_of_subset_closure
      · exact hi.subset.trans (by simp)
      · simp only [List.toFinset_cons,Finset.coe_insert]
        apply Set.insert_subset
        · apply hi.indep.mem_closure_iff'.mpr
          refine ⟨ha,?_⟩
          intro hind
          exfalso
          exact h ((hO _).mpr (by simpa using hind))
        · exact hi.subset_closure

lemma greedyOracle_rank (M : Matroid α) (O : Finset α → Bool)
    (hO : ∀ I,O I = true ↔ M.Indep (I : Set α)) (l : List α)
    (hE : ∀ a ∈ l,a ∈ M.E) :
    (greedyOracle O l).card = (M.eRk (l.toFinset : Set α)).toNat := by
  have h := (greedyOracle_correct M O hO l hE).encard_eq_eRk
  simpa using congrArg ENat.toNat h
end GreedyOracle

open scoped Classical

lemma queryFinset_exact {n : ℕ} (M₁ M₂ : Matroid (Fin n)) (O : IndependenceOracle n)
    (hO : ExactOracles M₁ M₂ O) (which : Bool) (I : Finset (Fin n)) :
    queryFinset O which I = true ↔ (if which then M₂ else M₁).Indep (I : Set (Fin n)) := by
  have h := hO which (fun i => decide (i ∈ I))
  have he : {i : Fin n | decide (i ∈ I) = true} = (I : Set (Fin n)) := by ext i; simp
  rw [he] at h
  exact h
lemma rankOracle_correct {n : ℕ} (M₁ M₂ : Matroid (Fin n)) (O : IndependenceOracle n)
    (hO : ExactOracles M₁ M₂ O) (hE₁ : M₁.E=Set.univ) (hE₂ : M₂.E=Set.univ)
    (which : Bool) (S : Finset (Fin n)) :
    rankOracle O which S = ((if which then M₂ else M₁).eRk (S : Set (Fin n))).toNat := by
  have hE : (if which then M₂ else M₁).E = Set.univ := by cases which <;> simpa
  have h := greedyOracle_rank (if which then M₂ else M₁) (queryFinset O which)
    (queryFinset_exact M₁ M₂ O hO which) ((List.finRange n).filter (fun i => decide (i ∈ S)))
    (by intro i _; simp [hE])
  have hs : (((List.finRange n).filter (fun i => decide (i ∈ S))).toFinset : Set (Fin n)) = S := by
    ext i; simp
  rw [hs] at h
  exact h

section SumRank
open Set
variable {α β : Type*} [sectionInstance121 : Fintype α] [sectionInstance122 : Fintype β]
omit sectionInstance121 sectionInstance122 in
lemma sum_eRk [Fintype α] [Fintype β] (M : Matroid α) (N : Matroid β) (S : Set (α ⊕ β)) :
    (M.sum N).eRk S = M.eRk (Sum.inl ⁻¹' S) + N.eRk (Sum.inr ⁻¹' S) := by
  obtain ⟨I,hI⟩ := M.exists_isBasis' (Sum.inl ⁻¹' S)
  obtain ⟨J,hJ⟩ := N.exists_isBasis' (Sum.inr ⁻¹' S)
  have hb : (M.sum N).IsBasis' (Sum.inl '' I ∪ Sum.inr '' J) S := by
    rw [Matroid.isBasis'_iff_isBasis_inter_ground,Matroid.sum_isBasis_iff]
    constructor
    · simpa [Set.preimage_image_eq _ Sum.inl_injective,Set.preimage_image_eq _ Sum.inr_injective]
        using hI.isBasis_inter_ground
    · simpa [Set.preimage_image_eq _ Sum.inl_injective,Set.preimage_image_eq _ Sum.inr_injective]
        using hJ.isBasis_inter_ground
  rw [hb.eRk_eq_encard,Set.encard_union_eq (Set.disjoint_image_inl_image_inr),
    Set.InjOn.encard_image Sum.inl_injective.injOn,
    Set.InjOn.encard_image Sum.inr_injective.injOn,hI.encard_eq_eRk,hJ.encard_eq_eRk]

lemma dual_rank_nat (M : Matroid α) (hE : M.E=Set.univ) (S : Set α) :
    (M✶.eRk S).toNat+M.eRank.toNat = S.ncard+(M.eRk Sᶜ).toNat := by
  have h := M.eRk_dual_add_eRank S (by simp [hE])
  rw [hE,← Set.compl_eq_univ_sdiff] at h
  have hh := congrArg ENat.toNat h
  rw [ENat.toNat_add (M✶.isRkFinite_set S).eRk_lt_top.ne
      ((M.eRank_ne_top_iff).mpr inferInstance),
    ENat.toNat_add (M.isRkFinite_set Sᶜ).eRk_lt_top.ne
      (Set.encard_ne_top_iff.mpr (Set.toFinite S))] at hh
  simpa only [Set.ncard,add_comm] using hh
end SumRank

open scoped Classical

lemma paired_rank_nat {n r : ℕ} (M₁ M₂ : Matroid (Fin n))
    (hE₂ : M₂.E=Set.univ) (hr₂ : M₂.eRank=(r:ℕ∞)) (S : Set (Fin n ⊕ Fin n)) :
    ((pairedMatroid M₁ M₂).eRk S).toNat+r =
      (M₁.eRk (Sum.inl ⁻¹' S)).toNat+(Sum.inr ⁻¹' S).ncard+
        (M₂.eRk (Sum.inr ⁻¹' S)ᶜ).toNat := by
  rw [pairedMatroid,sum_eRk,ENat.toNat_add
    (M₁.isRkFinite_set _).eRk_lt_top.ne (M₂✶.isRkFinite_set _).eRk_lt_top.ne]
  have h := dual_rank_nat M₂ hE₂ (Sum.inr ⁻¹' S)
  rw [hr₂,ENat.toNat_natCast] at h
  omega
lemma pairedDeficiencyOracle_correct {n r : ℕ} (M₁ M₂ : Matroid (Fin n))
    (O : IndependenceOracle n) (hO : ExactOracles M₁ M₂ O)
    (hE₁ : M₁.E=Set.univ) (hE₂ : M₂.E=Set.univ)
    (_ : M₁.eRank=(r:ℕ∞)) (hr₂ : M₂.eRank=(r:ℕ∞)) (S : Set (Fin n ⊕ Fin n)) :
    pairedDeficiencyOracle r O (Sum.inl ⁻¹' S).toFinset (Sum.inr ⁻¹' S).toFinset =
      n-((pairedMatroid M₁ M₂).eRk S).toNat := by
  have h := paired_rank_nat M₁ M₂ hE₂ hr₂ S
  unfold pairedDeficiencyOracle
  rw [rankOracle_correct M₁ M₂ O hO hE₁ hE₂,rankOracle_correct M₁ M₂ O hO hE₁ hE₂]
  simp only [Bool.false_eq_true,ite_false,ite_true,Set.coe_toFinset,Finset.coe_compl,
    Set.toFinset_card,Set.fintypeCard_eq_ncard]
  omega

section

open scoped BigOperators Classical
variable (n : ℕ) (hn : 0<n) (r : ℕ) (O : IndependenceOracle n) (N L : ℕ)
lemma rationalHistoryPositive_iff (h : List (PhaseSample n N)) :
    rationalHistoryPositive n N h ↔ HistoryPositive n N h := by
  unfold rationalHistoryPositive HistoryPositive
  constructor <;> intro hh j hj p q
  · have hs := hh j hj p q
    rw [←rationalStored_cast]
    exact_mod_cast hs
  · have hs := hh j hj p q
    rw [←rationalStored_cast] at hs
    exact_mod_cast hs
variable (M₁ M₂ : Matroid (Fin n)) (hO : ExactOracles M₁ M₂ O)
variable (hE₁ : M₁.E=Set.univ) (hE₂ : M₂.E=Set.univ)
variable (hr₁ : M₁.eRank=(r:ℕ∞)) (hr₂ : M₂.eRank=(r:ℕ∞))
include hO hE₁ hE₂ hr₁ hr₂
lemma oracleDeficiency_eq (S : Set (Fin n ⊕ Fin n)) :
    oracleDeficiency n r O S=n-((pairedMatroid M₁ M₂).eRk S).toNat :=
  pairedDeficiencyOracle_correct M₁ M₂ O hO hE₁ hE₂ hr₁ hr₂ S
lemma oracleAnneal_eq (j : ℕ) : oracleAnneal n r O j = rationalAnneal (pairedMatroid M₁ M₂) n j := by
  funext S
  simp only [oracleAnneal,rationalAnneal,oracleDeficiency_eq n r O M₁ M₂ hO hE₁ hE₂ hr₁ hr₂]
lemma oracleStepTree_eq (h : List (PhaseSample n N)) (j : ℕ) :
    oracleStepTree n hn r O N h j=actualStepTree n hn (pairedMatroid M₁ M₂) N h j := by
  unfold oracleStepTree actualStepTree
  rw [oracleAnneal_eq n r O M₁ M₂ hO hE₁ hE₂ hr₁ hr₂]
lemma oracleTraceTree_eq (h : List (PhaseSample n N)) (j cap : ℕ) :
    oracleTraceTree n hn r O N h j cap=actualTraceTree n hn (pairedMatroid M₁ M₂) N h j cap := by
  unfold oracleTraceTree actualTraceTree
  rw [oracleStepTree_eq n hn r O N M₁ M₂ hO hE₁ hE₂ hr₁ hr₂]
lemma oracleRestartTree_eq (h : List (PhaseSample n N)) (cap j : ℕ) :
    oracleRestartTree n hn r O N L h cap j = actualRestartTree n hn (pairedMatroid M₁ M₂) N L h cap j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [oracleRestartTree,actualRestartTree,ih,
      oracleTraceTree_eq n hn r O N M₁ M₂ hO hE₁ hE₂ hr₁ hr₂]
lemma oracleStartTree_eq (h : List (PhaseSample n N)) :
    oracleStartTree n hn r O N L h=actualStartTree n hn (pairedMatroid M₁ M₂) N L h := by
  unfold oracleStartTree actualStartTree
  rw [oracleRestartTree_eq n hn r O N L M₁ M₂ hO hE₁ hE₂ hr₁ hr₂]
lemma oraclePhaseTree_eq : oraclePhaseTree n hn r O N L=actualPhaseTree n hn (pairedMatroid M₁ M₂) N L := by
  funext h
  simp only [oraclePhaseTree,actualPhaseTree,rationalHistoryPositive_iff,
    oracleStartTree_eq n hn r O N L M₁ M₂ hO hE₁ hE₂ hr₁ hr₂,
    oracleStepTree_eq n hn r O N M₁ M₂ hO hE₁ hE₂ hr₁ hr₂]
lemma oracleEstimate_eq (h : List (PhaseSample n N)) :
    oracleEstimate n r O N L h=rationalEstimate n M₁ M₂ N L h := by
  simp only [oracleEstimate,rationalEstimate,
    oracleDeficiency_eq n r O M₁ M₂ hO hE₁ hE₂ hr₁ hr₂]
lemma oracleGuard_eq (h : List (PhaseSample n N)) :
    oracleGuard n r O N L h=rationalGuard n M₁ M₂ N L h := by
  funext x
  simp only [oracleGuard,rationalGuard,Witnessed,
    oracleDeficiency_eq n r O M₁ M₂ hO hE₁ hE₂ hr₁ hr₂,
    oracleEstimate_eq n r O N L M₁ M₂ hO hE₁ hE₂ hr₁ hr₂]
  split_ifs <;> simp_all
lemma oracleWitnessTree_eq (h : List (PhaseSample n N)) :
    oracleWitnessTree n hn r O N L h=rationalWitnessTree n hn M₁ M₂ N L h := by
  simp only [oracleWitnessTree,rationalWitnessTree,rationalHistoryPositive_iff,
    oracleRestartTree_eq n hn r O N L M₁ M₂ hO hE₁ hE₂ hr₁ hr₂]
theorem oracleAlgorithmTree_eq : oracleAlgorithmTree n hn r O N L=rationalAlgorithmTree n hn M₁ M₂ N L := by
  simp only [oracleAlgorithmTree,rationalAlgorithmTree,
    oraclePhaseTree_eq n hn r O N L M₁ M₂ hO hE₁ hE₂ hr₁ hr₂,
    oracleWitnessTree_eq n hn r O N L M₁ M₂ hO hE₁ hE₂ hr₁ hr₂,
    oracleGuard_eq n r O N L M₁ M₂ hO hE₁ hE₂ hr₁ hr₂]

end

open scoped BigOperators Classical
lemma commonBaseCount_empty (M₁ M₂ : Matroid (Fin 0)) : commonBaseCount M₁ M₂=1 := by
  have base (M : Matroid (Fin 0)) : M.IsBase ∅ := by
    obtain ⟨B,hB⟩ := M.exists_isBase
    have he : B=∅ := Set.eq_empty_of_isEmpty B
    simpa only [he] using hB
  let : Nonempty {A : Finset (Fin 0) // M₁.IsBase (A:Set (Fin 0)) ∧ M₂.IsBase (A:Set (Fin 0))} :=
    ⟨⟨∅,by simpa using And.intro (base M₁) (base M₂)⟩⟩
  unfold commonBaseCount
  exact Nat.card_unique

open scoped BigOperators Classical

section
namespace DrawTree
open scoped BigOperators Classical
variable {A B : Type*}

lemma Reindexed.refl (t : DrawTree A) : Reindexed t t := by
  induction t with
  | leaf a => exact .leaf a
  | draw v k ih => exact .draw v k k (Equiv.refl _) ih
lemma Reindexed.symm {t u : DrawTree A} (h : Reindexed t u) : Reindexed u t := by
  induction h with
  | leaf a => exact .leaf a
  | draw v k l e h ih =>
    apply Reindexed.draw v l k e.symm
    intro i
    simpa using ih (e.symm i)
lemma Reindexed.bind {t u : DrawTree A} {k l : A → DrawTree B}
    (ht : Reindexed t u) (hk : ∀ a,Reindexed (k a) (l a)) :
    Reindexed (t.bind k) (u.bind l) := by
  induction ht with
  | leaf a => exact hk a
  | draw v a b e h ih => exact .draw v _ _ e ih
lemma Reindexed.map {t u : DrawTree A} (h : Reindexed t u) (f : A → B) :
    Reindexed (t.map f) (u.map f) := h.bind (fun a => .leaf (f a))
lemma uniformVia_reindexed (A : Type*) [Fintype A] [Nonempty A]
    (e : Fin (Fintype.card A) ≃ A) : Reindexed (uniformVia A e) (uniformChoice A) := by
  let h : Fintype.card A-1+1=Fintype.card A := by have hh := Fintype.card_pos (α := A); omega
  let c := finCongr h
  let p := c.trans (e.trans ((Fintype.equivFin A).trans c.symm))
  apply Reindexed.draw _ _ _ p
  intro i
  have he : (Fintype.equivFin A).symm (Fin.cast h (p i))=e (Fin.cast h i) := by simp [p,c]
  simpa only [he] using Reindexed.leaf (e (Fin.cast h i))
lemma Reindexed.fits {t u : DrawTree A} (h : Reindexed t u) (H M : ℕ)
    (ht : Fits H M t) : Fits H M u := by
  induction h generalizing M with
  | leaf a => trivial
  | draw v k l e h ih =>
    cases M with
    | zero => exact False.elim ht
    | succ M =>
      refine ⟨ht.1,fun i => ?_⟩
      simpa using ih (e.symm i) M (ht.2 (e.symm i))
lemma Reindexed.all {t u : DrawTree A} (h : Reindexed t u) (P : A → Prop)
    (ht : All P t) : All P u := by
  induction h with
  | leaf a => exact ht
  | draw v k l e h ih =>
    intro i
    simpa using ih (e.symm i) (ht (e.symm i))
lemma Reindexed.run_expectation {t u : DrawTree A} (h : Reindexed t u) (H D M : ℕ)
    (ht : Fits H M t) (φ : A → ℝ) :
    uniformAverage (fun bits => optionValue φ (run H D M t bits))=
      uniformAverage (fun bits => optionValue φ (run H D M u bits)) := by
  induction h generalizing M with
  | leaf a => rfl
  | draw v k l e h ih =>
    cases M with
    | zero => exact False.elim ht
    | succ M =>
      rw [run_draw_average H D M v k ht.1 φ,run_draw_average H D M v l ht.1 φ]
      congr 1
      have he : ∀ i,uniformAverage (fun bits => optionValue φ (run H D M (k i) bits))=
          uniformAverage (fun bits => optionValue φ (run H D M (l (e i)) bits)) :=
        fun i => ih i M (ht.2 i)
      simp_rw [he]
      exact uniformAverage_equiv e (fun i => uniformAverage (fun bits => optionValue φ (run H D M (l i) bits)))
lemma Reindexed.run_observable {t u : DrawTree A} (h : Reindexed t u) (H D M : ℕ)
    (ht : Fits H M t) (φ : Option A → ℝ) :
    uniformAverage (fun bits => φ (run H D M t bits))=
      uniformAverage (fun bits => φ (run H D M u bits)) := by
  have hf : ∀ x : Option A,φ x=optionValue (fun a => φ (some a)-φ none) x+φ none := by
    intro x; cases x <;> simp [optionValue]
  have he (v : DrawTree A) :
      (fun bits => φ (run H D M v bits))=
        (fun bits => optionValue (fun a => φ (some a)-φ none) (run H D M v bits)+φ none) :=
    funext (fun bits => hf _)
  rw [he t,he u,uniformAverage_add,uniformAverage_add,h.run_expectation H D M ht]
lemma Reindexed.optionBind {t u : DrawTree (Option A)} {k l : A → DrawTree (Option B)}
    (ht : Reindexed t u) (hk : ∀ a,Reindexed (k a) (l a)) :
    Reindexed (t.optionBind k) (u.optionBind l) := by
  apply ht.bind
  intro a; cases a with
  | none => exact .leaf none
  | some a => exact hk a
lemma Reindexed.iterate {t u : A → DrawTree (Option A)} (h : ∀ a,Reindexed (t a) (u a))
    (k : ℕ) (a : A) : Reindexed (iterate t k a) (iterate u k a) := by
  induction k with
  | zero => exact .leaf (some a)
  | succ k ih => exact ih.optionBind h
lemma Reindexed.sample [Fintype A] {t u : A → DrawTree A} (h : ∀ a,Reindexed (t a) (u a))
    (k : ℕ) (a : A) : Reindexed (sample t k a) (sample u k a) := by
  induction k generalizing a with
  | zero => exact .leaf a
  | succ k ih => exact (h a).bind (fun x => (ih x).map (fun v => (a,v)))
lemma Reindexed.history {K L : List A → DrawTree (Option A)}
    (h : ∀ a,Reindexed (K a) (L a)) (k : ℕ) (a : List A) :
    Reindexed (history K k a) (history L k a) := by
  induction k generalizing a with
  | zero => exact .leaf (some a)
  | succ k ih => exact (h a).optionBind (fun x => ih (a++[x]))
end DrawTree
lemma hittingTree_reindexed {X : Type*} [Fintype X] {t u : X → DrawTree X}
    (h : ∀ x,DrawTree.Reindexed (t x) (u x)) (A : X → Prop) (k : ℕ) (x : X) :
    DrawTree.Reindexed (hittingTree t A k x) (hittingTree u A k x) := by
  classical
  induction k generalizing x with
  | zero => exact .leaf none
  | succ k ih =>
    apply (h x).bind
    intro y
    by_cases hy : A y
    · simp only [dite_eq_left hy]; exact .leaf _
    · simp only [dite_eq_right hy]; exact ih y

open scoped BigOperators Classical
variable (n : ℕ) (hn : 0<n) (r : ℕ) (O : IndependenceOracle n) (N L : ℕ)
local notation "GS" => pairedSlots n
lemma canonicalMetropolis_reindexed (w : ((Fin n ⊕ Fin n) × (Fin n ⊕ Fin n)) →
    ((Fin n ⊕ Fin n) × (Fin n ⊕ Fin n)) → ℚ) (f : Set (Fin n ⊕ Fin n) → ℚ)
    (S : ChainIndex GS) : DrawTree.Reindexed (canonicalMetropolis n hn w f S)
      (rationalMetropolis GS (pairedSlots_fresh n) (pairedSlots_ne_nil n hn) (pairedSlots_cover n) w f S) := by
  let : Nonempty (ExchangeChoice S.val) := Fintype.card_pos_iff.mp (by
    rw [exchangeChoice_card GS (pairedSlots_fresh n) (pairedSlots_cover n),pairedSlots_length]; positivity)
  apply (DrawTree.Reindexed.refl (DrawTree.bernoulli (1/2))).bind
  intro lazy
  cases lazy with
  | true => exact .leaf S
  | false =>
    apply (DrawTree.uniformVia_reindexed _ (canonicalExchangeEnumeration n S.val)).bind
    intro a; exact .refl _
lemma canonicalStepTree_reindexed (h : List (PhaseSample n N)) (j : ℕ) (S : ChainIndex GS) :
    DrawTree.Reindexed (canonicalStepTree n hn r O N h j S) (oracleStepTree n hn r O N h j S) :=
  canonicalMetropolis_reindexed n hn _ _ S
lemma canonicalTraceTree_reindexed (h : List (PhaseSample n N)) (j cap : ℕ) (S : PlainIndex GS) :
    DrawTree.Reindexed (canonicalTraceTree n hn r O N h j cap S) (oracleTraceTree n hn r O N h j cap S) :=
  hittingTree_reindexed (canonicalStepTree_reindexed n hn r O N h j) _ _ _
lemma canonicalRestartTree_reindexed (h : List (PhaseSample n N)) (cap j : ℕ) :
    DrawTree.Reindexed (canonicalRestartTree n hn r O N L h cap j) (oracleRestartTree n hn r O N L h cap j) := by
  let := plainIndex_nonempty GS (pairedSlots_fresh n) (pairedSlots_cover n)
  induction j with
  | zero => exact (DrawTree.uniformVia_reindexed _ (canonicalPlainEnumeration n)).map some
  | succ j ih => exact ih.optionBind (fun S => DrawTree.Reindexed.iterate (canonicalTraceTree_reindexed n hn r O N h (j+1) cap) _ S)
lemma canonicalStartTree_reindexed (h : List (PhaseSample n N)) :
    DrawTree.Reindexed (canonicalStartTree n hn r O N L h) (oracleStartTree n hn r O N L h) :=
  (canonicalRestartTree_reindexed n hn r O N L h _ _).map _
lemma canonicalPhaseTree_reindexed (h : List (PhaseSample n N)) :
    DrawTree.Reindexed (canonicalPhaseTree n hn r O N L h) (oraclePhaseTree n hn r O N L h) := by
  unfold canonicalPhaseTree oraclePhaseTree
  split_ifs
  · exact (canonicalStartTree_reindexed n hn r O N L h).optionBind (fun S =>
      (DrawTree.Reindexed.sample (canonicalStepTree_reindexed n hn r O N h h.length) _ S).map some)
  · exact .leaf none
lemma canonicalWitnessTree_reindexed (h : List (PhaseSample n N)) :
    DrawTree.Reindexed (canonicalWitnessTree n hn r O N L h) (oracleWitnessTree n hn r O N L h) := by
  unfold canonicalWitnessTree oracleWitnessTree
  split_ifs
  · exact canonicalRestartTree_reindexed n hn r O N L h _ _
  · exact .leaf none
lemma canonicalAlgorithmTree_reindexed :
    DrawTree.Reindexed (canonicalAlgorithmTree n hn r O N L) (oracleAlgorithmTree n hn r O N L) :=
  (DrawTree.Reindexed.history (canonicalPhaseTree_reindexed n hn r O N L) L []).optionBind
    (fun h => (canonicalWitnessTree_reindexed n hn r O N L h).map _)

end

section CanonicalFair
open scoped BigOperators Classical
lemma uniformAverage_independent_eq {X Y Z : Type*} [Fintype X] [Fintype Y]
    (f : X → Z) (g : Y → Z)
    (h : ∀ φ : Z → ℝ,uniformAverage (fun x => φ (f x))=uniformAverage (fun y => φ (g y)))
    (k : ℕ) (F : (Fin k → Z) → ℝ) :
    uniformAverage (fun xs : Fin k → X => F (fun i => f (xs i)))=
      uniformAverage (fun ys : Fin k → Y => F (fun i => g (ys i))) := by
  induction k with
  | zero =>
    have hf : ∀ xs : Fin 0 → X,(fun i => f (xs i))=(fun i : Fin 0 => Fin.elim0 i) := by
      intro xs; funext i; exact Fin.elim0 i
    have hg : ∀ ys : Fin 0 → Y,(fun i => g (ys i))=(fun i : Fin 0 => Fin.elim0 i) := by
      intro ys; funext i; exact Fin.elim0 i
    simp_rw [hf,hg,uniformAverage_const]
  | succ k ih =>
    have hf (x : X) (xs : Fin k → X) :
        (fun i : Fin (k+1) => f ((Fin.cons x xs : Fin (k+1) → X) i))=Fin.cons (f x) (fun i => f (xs i)) := by
      funext i; refine Fin.cases ?_ (fun j => ?_) i <;> rfl
    have hg (y : Y) (ys : Fin k → Y) :
        (fun i : Fin (k+1) => g ((Fin.cons y ys : Fin (k+1) → Y) i))=Fin.cons (g y) (fun i => g (ys i)) := by
      funext i; refine Fin.cases ?_ (fun j => ?_) i <;> rfl
    rw [uniformAverage_fin_succ,uniformAverage_fin_succ]
    simp_rw [hf,hg]
    have hi (x : X) := ih (fun zs => F (Fin.cons (f x) zs))
    simp_rw [hi]
    exact h (fun z => uniformAverage (fun ys : Fin k → Y => F (Fin.cons z (fun i => g (ys i)))))
variable (n : ℕ) (hn : 0<n) (r : ℕ) (O : IndependenceOracle n) (N L : ℕ)
variable (M₁ M₂ : Matroid (Fin n)) (hO : ExactOracles M₁ M₂ O)
variable (hE₁ : M₁.E=Set.univ) (hE₂ : M₂.E=Set.univ)
variable (hr₁ : M₁.eRank=(r:ℕ∞)) (hr₂ : M₂.eRank=(r:ℕ∞))
include hO hE₁ hE₂ hr₁ hr₂ in
lemma canonicalAlgorithmTree_to_rational :
    DrawTree.Reindexed (canonicalAlgorithmTree n hn r O N L) (rationalAlgorithmTree n hn M₁ M₂ N L) := by
  rw [←oracleAlgorithmTree_eq n hn r O N L M₁ M₂ hO hE₁ hE₂ hr₁ hr₂]
  exact canonicalAlgorithmTree_reindexed n hn r O N L
include hO hE₁ hE₂ hr₁ hr₂ in
lemma canonicalAlgorithmTree_fits (hN : 0<N) :
    DrawTree.Fits (drawWordBound n N L) (algorithmDrawBound n N L) (canonicalAlgorithmTree n hn r O N L) :=
  (canonicalAlgorithmTree_to_rational n hn r O N L M₁ M₂ hO hE₁ hE₂ hr₁ hr₂).symm.fits _ _
    (rationalAlgorithmTree_fits n hn M₁ M₂ N L hN)
include hO hE₁ hE₂ hr₁ hr₂ in
lemma canonicalFairOutput_all (bits : FairBank n N L) :
    0≤canonicalFairOutput n hn r O N L bits ∧
      (commonBaseCount M₁ M₂=0 → canonicalFairOutput n hn r O N L bits=0) := by
  have ht := (canonicalAlgorithmTree_to_rational n hn r O N L M₁ M₂ hO hE₁ hE₂ hr₁ hr₂).symm.all _
    (rationalAlgorithmTree_all n hn M₁ M₂ N L)
  unfold canonicalFairOutput
  generalize he : DrawTree.run _ _ _ _ bits=a
  cases a with
  | none => simp
  | some a =>
    cases a with
    | none => simp
    | some z =>
      simp only [Option.join_some,Option.getD_some]
      have hz := DrawTree.run_all _ _ _ _ _ ht bits (some z) he z rfl
      exact ⟨hz.1,hz.2 hE₂ (hr₁.trans hr₂.symm)⟩
include hO hE₁ hE₂ hr₁ hr₂ in
lemma canonicalFairOutput_law (hN : 0<N) (φ : ℚ → ℝ) :
    uniformAverage (fun bits : FairBank n N L => φ (canonicalFairOutput n hn r O N L bits))=
      uniformAverage (fun bits : FairBank n N L => φ (fairOutput n hn M₁ M₂ N L bits)) :=
  (canonicalAlgorithmTree_to_rational n hn r O N L M₁ M₂ hO hE₁ hE₂ hr₁ hr₂).run_observable _ _ _
    (canonicalAlgorithmTree_fits n hn r O N L M₁ M₂ hO hE₁ hE₂ hr₁ hr₂ hN)
    (fun a : Option (Option ℚ) => φ (a.join.getD 0))
include hO hE₁ hE₂ hr₁ hr₂ in
lemma canonicalAmplifiedOutput_law (hN : 0<N) (δ : ℚ) (φ : ℚ → ℝ) :
    uniformAverage (fun bits => φ (canonicalAmplifiedOutput n hn r O N L δ bits))=
      uniformAverage (fun bits => φ (amplifiedOutput n hn M₁ M₂ N L δ bits)) :=
  uniformAverage_independent_eq (canonicalFairOutput n hn r O N L) (fairOutput n hn M₁ M₂ N L)
    (canonicalFairOutput_law n hn r O N L M₁ M₂ hO hE₁ hE₂ hr₁ hr₂ hN) _
    (fun z => φ (rationalMedian (List.ofFn z)))
include hO hE₁ hE₂ hr₁ hr₂ in
lemma canonicalAmplifiedOutput_all (δ : ℚ) (bits : Fin (repetitionCount δ) → FairBank n N L) :
    0≤canonicalAmplifiedOutput n hn r O N L δ bits ∧
      (commonBaseCount M₁ M₂=0 → canonicalAmplifiedOutput n hn r O N L δ bits=0) := by
  constructor
  · apply rationalMedian_all (fun z => 0≤z) _ (by norm_num)
    intro z hz
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hz
    exact (canonicalFairOutput_all n hn r O N L M₁ M₂ hO hE₁ hE₂ hr₁ hr₂ (bits i)).1
  · intro hZ
    apply rationalMedian_all (fun z => z=0) _ rfl
    intro z hz
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hz
    exact (canonicalFairOutput_all n hn r O N L M₁ M₂ hO hE₁ hE₂ hr₁ hr₂ (bits i)).2 hZ
end CanonicalFair

open scoped BigOperators Classical

theorem canonical_bounded_fair_experiment (n r : ℕ) (O : IndependenceOracle n)
    (M₁ M₂ : Matroid (Fin n)) (hO : ExactOracles M₁ M₂ O)
    (hE₁ : M₁.E=Set.univ) (hE₂ : M₂.E=Set.univ)
    (hr₁ : M₁.eRank=(r:ℕ∞)) (hr₂ : M₂.eRank=(r:ℕ∞))
    (ε δ : ℚ) (hε0 : 0<ε) (hε1 : ε<1) (hδ : 0<δ) :
    (∀ bits : FPRASBank n ε δ,0≤canonicalBoundedOutput n r O ε δ bits ∧
      (commonBaseCount M₁ M₂=0 → canonicalBoundedOutput n r O ε δ bits=0)) ∧
    1-(δ:ℝ)≤uniformAverage (fun bits : FPRASBank n ε δ =>
      if relativeAccuracy ε (commonBaseCount M₁ M₂) (canonicalBoundedOutput n r O ε δ bits) then (1:ℝ) else 0) := by
  by_cases hn : 0<n
  · constructor
    · intro bits
      simp only [canonicalBoundedOutput,dite_eq_left hn]
      exact canonicalAmplifiedOutput_all n hn r O _ _ M₁ M₂ hO hE₁ hE₂ hr₁ hr₂ δ bits
    · simp only [canonicalBoundedOutput,dite_eq_left hn]
      have hlaw := canonicalAmplifiedOutput_law n hn r O
        (sampleCount n (annealLength n (accuracyExponent ε)) ε)
        (annealLength n (accuracyExponent ε)) M₁ M₂ hO hE₁ hE₂ hr₁ hr₂
        (by unfold sampleCount; omega) δ
        (fun z => if relativeAccuracy ε (commonBaseCount M₁ M₂) z then (1:ℝ) else 0)
      rw [hlaw]
      exact (bounded_fair_experiment n hn M₁ M₂ hE₁ hE₂ (hr₁.trans hr₂.symm) ε δ hε0 hε1 hδ).2
  · have hn0 : n=0 := by omega
    subst n
    have ho : ∀ bits : FPRASBank 0 ε δ,canonicalBoundedOutput 0 r O ε δ bits=1 := by intro bits; simp [canonicalBoundedOutput]
    constructor
    · intro bits
      rw [ho bits,commonBaseCount_empty]
      norm_num
    · have hac : 1-ε≤(1:ℚ) ∧ (1:ℚ)≤1+ε := by constructor <;> linarith
      simpa only [ho,commonBaseCount_empty,relativeAccuracy,Nat.cast_one,mul_one,ite_eq_left hac,
        uniformAverage_const] using (sub_le_self (1:ℝ) (by exact_mod_cast hδ.le : (0:ℝ)≤δ))

open scoped BigOperators Classical

lemma uniformAverage_indicator_card {X : Type*} [Fintype X] (P : X → Prop) :
    uniformAverage (fun x => if P x then (1:ℝ) else 0)=
      (Nat.card {x // P x}:ℝ)/(Fintype.card X:ℝ) := by
  simp [uniformAverage,Nat.card_eq_fintype_card,Fintype.card_subtype]

open scoped BigOperators Classical

open scoped Classical
lemma uniformAverage_bitEmbedding (m B : ℕ) (f : Fin m → Fin B)
    (hf : Function.Injective f) (φ : BitWord m → ℝ) :
    uniformAverage (fun w : BitWord B => φ (fun i => w (f i)))=uniformAverage φ := by
  have hm : m≤B := by simpa using Fintype.card_le_of_injective f hf
  let g : Fin m → Fin B := fun i => ⟨i.val,lt_of_lt_of_le i.isLt hm⟩
  have hg : Function.Injective g := by
    intro i j h
    apply Fin.ext
    exact congrArg (fun x : Fin B => x.val) h
  obtain ⟨σ,hσ⟩ := Equiv.Perm.exists_extending_pair g f hg hf
  let e : BitWord B ≃ BitWord B := Equiv.arrowCongr σ.symm (Equiv.refl Bool)
  have he (w : BitWord B) : (fun i => w (f i))=bitPrefix m B hm (e w) := by
    funext i
    change w (f i)=w (σ (g i))
    rw [hσ]
  simp_rw [he]
  rw [uniformAverage_equiv e (fun w => φ (bitPrefix m B hm w))]
  exact uniformAverage_bitPrefix m B hm φ

end

namespace MachineCode


namespace SizePolynomial
lemma bound (p : SizePolynomial) (x : ℕ) : p.eval x≤p.coefficient*(x+1)^p.degree := by
  induction p with
  | constant c => simp [eval,coefficient,degree]
  | input => simp [eval,coefficient,degree]
  | add p q ihp ihq =>
    have hp := Nat.pow_le_pow_right (by omega : 1≤x+1) (Nat.le_add_right p.degree q.degree)
    have hq := Nat.pow_le_pow_right (by omega : 1≤x+1) (Nat.le_add_left q.degree p.degree)
    dsimp only [eval,coefficient,degree]
    calc
      _ ≤ p.coefficient*(x+1)^(p.degree+q.degree)+q.coefficient*(x+1)^(p.degree+q.degree) :=
        Nat.add_le_add (ihp.trans (Nat.mul_le_mul_left _ hp)) (ihq.trans (Nat.mul_le_mul_left _ hq))
      _ = _ := by ring
  | mul p q ihp ihq =>
    dsimp only [eval,coefficient,degree]
    calc
      _ ≤ (p.coefficient*(x+1)^p.degree)*(q.coefficient*(x+1)^q.degree) := Nat.mul_le_mul ihp ihq
      _ = _ := by rw [pow_add]; ring
end SizePolynomial

open Expression

open Expression

open Expression

open Expression

open Expression

open Expression
end MachineCode

namespace MachineCode

open Expression
open scoped Classical

open Expression

open Expression
open scoped Classical

open Expression
open scoped Classical

open Expression

open Expression
open scoped Classical

open Expression
open scoped Classical

open Expression

open Expression Effect

open Expression
open scoped Classical

open Expression

open Expression Effect

open Expression
open Expression Effect

open Expression

open Expression
lemma master_pos (n r : ℕ) (ε δ : ℚ) : 0 < masterParameter n r ε δ := by
  unfold masterParameter; omega

open Expression Effect

open Expression
lemma SizePolynomial.monomial_bound (p : SizePolynomial) (T : ℕ) (hT : 0<T) :
    p.eval T ≤ (p.coefficient*2^p.degree+1)*T^p.degree := by
  have h : T+1≤2*T := by omega
  calc
    p.eval T ≤ p.coefficient*(T+1)^p.degree := p.bound T
    _ ≤ p.coefficient*(2*T)^p.degree := by gcongr
    _ ≤ (p.coefficient*2^p.degree+1)*T^p.degree := by
      rw [mul_pow,←Nat.mul_assoc]
      exact Nat.mul_le_mul_right _ (Nat.le_add_right _ _)

lemma physicalPosition_injective (start m B : ℕ) (h : start+3*m+1≤B) :
    Function.Injective (physicalPosition start m B h) := by
  intro i j he
  have hh := congrArg Fin.val he
  dsimp only [physicalPosition] at hh
  apply Fin.ext
  have hi := i.isLt
  have hj := j.isLt
  omega
lemma physicalWord_finite (start m B : ℕ) (h : start+3*m+1≤B) (w : BitWord B) :
    physicalWord start m (finiteBits w)=fun i => w (physicalPosition start m B h i) := by
  funext i
  unfold physicalWord finiteBits physicalPosition
  simp only [dite_eq_left (show start+3*(m-1-i.val)+1<B by have hi := i.isLt; omega)]
lemma physicalWord_law (start m B : ℕ) (h : start+3*m+1≤B) (φ : BitWord m → ℝ) :
    uniformAverage (fun w : BitWord B => φ (physicalWord start m (finiteBits w)))=uniformAverage φ := by
  simp_rw [physicalWord_finite start m B h]
  exact uniformAverage_bitEmbedding m B _ (physicalPosition_injective start m B h) φ

open Expression

open Expression Effect
open scoped Classical

open Expression

open Expression
open scoped Classical

open Expression

open scoped Classical

lemma physical_accuracy {n : ℕ} (r : ℕ) (M₁ M₂ : Matroid (Fin n))
    (O : IndependenceOracle n) (ε δ : ℚ)
    (hO : ExactOracles M₁ M₂ O) (hE₁ : M₁.E=Set.univ) (hE₂ : M₂.E=Set.univ)
    (hr₁ : M₁.eRank=(r:ℕ∞)) (hr₂ : M₂.eRank=(r:ℕ∞))
    (hε : 0<ε) (hε1 : ε<1) (hδ : 0<δ)
    (v : BitWord (fairBitCount n ε δ) → ℚ) (hv : OutputCertificate r M₁ M₂ O ε δ v)
    (start B : ℕ) (hstart : start+3*fairBitCount n ε δ+1≤B) :
    (1-δ)*(2:ℚ)^B ≤ (Nat.card {bits : BitWord B // relativeAccuracy ε (commonBaseCount M₁ M₂)
      (v (physicalWord start (fairBitCount n ε δ) (finiteBits bits)))}:ℚ) := by
  have h := (canonical_bounded_fair_experiment n r O M₁ M₂ hO hE₁ hE₂ hr₁ hr₂ ε δ hε hε1 hδ).2
  rw [←hv.2.2 (fun z => if relativeAccuracy ε (commonBaseCount M₁ M₂) z then (1:ℝ) else 0)] at h
  rw [←physicalWord_law start (fairBitCount n ε δ) B hstart
    (fun w => if relativeAccuracy ε (commonBaseCount M₁ M₂) (v w) then (1:ℝ) else 0)] at h
  rw [uniformAverage_indicator_card] at h
  have hcard : Fintype.card (BitWord B)=2^B := by simp [BitWord]
  rw [hcard,Nat.cast_pow,Nat.cast_ofNat] at h
  have hh := (le_div_iff₀ (by positivity : (0:ℝ)<2^B)).mp h
  exact_mod_cast hh
end MachineCode
end CommonBasesFPRAS

open CommonBasesFPRAS CommonBasesFPRAS.MachineCode

theorem common_bases_fpras_oai : CommonBasesFPRAS.MainTheorem := by
  classical
  obtain ⟨fp,fq,hs⟩ := frozen_uniform_safe
  let p := totalResourcePoly fp fq
  refine ⟨1,fprasBlock.size,fprasBlock.code,p.coefficient*2^p.degree+1,p.degree,by omega,?_⟩
  intro n r M₁ M₂ O ε δ hE₁ hE₂ hr₁ hr₂ hO hε hε1 hδ hδ1
  have hh := hs n r M₁ M₂ O ε δ hO hE₁ hE₂ hr₁ hε
  let B := resourceBound (p.coefficient*2^p.degree+1) p.degree n r ε δ
  have hB : p.eval (masterParameter n r ε δ)≤B :=
    p.monomial_bound _ (master_pos n r ε δ)
  obtain ⟨v,start,hv,hstart,he⟩ := frozen_machine fp fq n r M₁ M₂ O ε δ hO hE₁ hE₂ hr₁ hr₂ hε hh.1 hh.2 B hB
  constructor
  · intro bits
    have h := he bits
    refine ⟨?_,h.2.1,h.2.2,?_⟩
    · rw [h.1]; rfl
    · intro z hz
      rw [h.1] at hz
      have hez := Option.some.inj hz
      subst z
      exact hv.2.1 _
  · have ha := physical_accuracy r M₁ M₂ O ε δ hO hE₁ hE₂ hr₁ hr₂ hε hε1 hδ v hv start B hstart
    have hpred (bits : BitWord B) :
        (∃ z,(execution fprasBlock.code O (initialConfig 1 fprasBlock.size n r ε δ) (finiteBits bits) B).output=some z ∧
          relativeAccuracy ε (commonBaseCount M₁ M₂) z) ↔
        relativeAccuracy ε (commonBaseCount M₁ M₂) (v (physicalWord start (fairBitCount n ε δ) (finiteBits bits))) := by
      rw [(he (finiteBits bits)).1]
      simp only [Option.some.injEq,exists_eq_left']
    change (1-δ)*(2:ℚ)^B ≤ (Nat.card {bits : BitWord B // ∃ z,
      (execution fprasBlock.code O (initialConfig 1 fprasBlock.size n r ε δ) (finiteBits bits) B).output=some z ∧
        relativeAccuracy ε (commonBaseCount M₁ M₂) z}:ℚ)
    simpa only [hpred] using ha

end OAI
end

theorem solution : type_of% @OAI.common_bases_fpras_oai := @OAI.common_bases_fpras_oai
