-- Prove2me | solution 1 for QuantumBipartiteTesting.Bipartiteness.partition_power_sum_cancellation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T14:15:34.041778+00:00
-- url     : https://prove2.me/submissions/f1545e58-7d29-484d-b3b5-97d8930b90ec

import Theorems.Thm_QuantumBipartiteTesting_Bipartiteness_partition_mobius_cancellation

namespace QuantumBipartiteTesting.Bipartiteness.PowerProof
noncomputable section
open Finset
attribute [local instance] Classical.propDecidable Classical.decEq
set_option maxHeartbeats 1000000
set_option maxRecDepth 2000
set_option backward.isDefEq.respectTransparency.types false

private def PSetoid {k : ℕ} (p : Partition k) : Setoid (Fin k) := ⟨_,p.property⟩
private def Class {k : ℕ} (p : Partition k) (i : Fin k) : Finset (Fin k) :=
  univ.filter fun j => p.val i j = true

private lemma self_class {k : ℕ} (p : Partition k) (i : Fin k) : i ∈ Class p i := by
  exact mem_filter.mpr ⟨mem_univ _,p.property.refl i⟩
private lemma class_mem {k : ℕ} (p : Partition k) (i : Fin k) : Class p i ∈ Blocks p :=
  mem_image.mpr ⟨i,mem_univ _,rfl⟩
private lemma class_eq {k : ℕ} (p : Partition k) (i j : Fin k) :
    Class p i = Class p j ↔ p.val i j = true := by
  constructor
  · intro h
    have hh := h ▸ self_class p i
    exact p.property.symm ((mem_filter.mp hh).2)
  · intro hij
    ext x
    simp only [Class,mem_filter,mem_univ,true_and]
    exact ⟨fun h => p.property.trans (p.property.symm hij) h,
      fun h => p.property.trans hij h⟩

private def blockEquiv {k : ℕ} (p : Partition k) :
    Quotient (PSetoid p) ≃ {S // S ∈ Blocks p} where
  toFun q := Quotient.liftOn q (fun i => ⟨Class p i,class_mem p i⟩)
    (fun i j hij => Subtype.ext ((class_eq p i j).mpr hij))
  invFun S := Quotient.mk (PSetoid p) (mem_image.mp S.property).choose
  left_inv q := by
    induction q using Quotient.inductionOn with
    | h i =>
      apply Quotient.sound
      have hh := (mem_image.mp (class_mem p i)).choose_spec.2
      exact (class_eq p _ i).mp hh
  right_inv S := by
    apply Subtype.ext
    exact (mem_image.mp S.property).choose_spec.2

private def labelEquiv {k : ℕ} (p : Partition k) :
    (Quotient (PSetoid p) → ZMod 2) ≃
      {x : Fin k → ZMod 2 // ∀ i j, p.val i j = true → x i = x j} where
  toFun f := ⟨fun i => f (Quotient.mk (PSetoid p) i),
    fun i j hij => congrArg f (Quotient.sound hij)⟩
  invFun x := fun q => Quotient.liftOn q x.val x.property
  left_inv f := by
    funext q
    induction q using Quotient.inductionOn with
    | h i => rfl
  right_inv x := by apply Subtype.ext; rfl

private lemma constant_labels_card {k : ℕ} (p : Partition k) :
    Fintype.card {x : Fin k → ZMod 2 // ∀ i j, p.val i j = true → x i = x j} =
      2^(Blocks p).card := by
  rw [← Fintype.card_congr (labelEquiv p),Fintype.card_fun,ZMod.card]
  have hh : Fintype.card (Quotient (PSetoid p)) = (Blocks p).card := by
    rw [Fintype.card_congr (blockEquiv p),Fintype.card_coe]
  rw [hh]

private def Constraints {k e : ℕ} (u v : Fin e → Fin k) :
    (Fin k → ZMod 2) →+ (Fin e → ZMod 2) where
  toFun x := fun j => x (u j)-x (v j)
  map_zero' := by ext j; simp
  map_add' x y := by ext j; simp; ring

private lemma sparse_separating_label {k e : ℕ} (p : Partition k)
    (u v : Fin e → Fin k) (he : e+(Blocks p).card < k) :
    ∃ x : Fin k → ZMod 2, (∀ j, x (u j) = x (v j)) ∧
      ¬ (∀ i j, p.val i j = true → x i = x j) := by
  let f := Constraints u v
  by_contra hn
  push Not at hn
  have hconst : ∀ x : f.ker, ∀ i j, p.val i j = true → x.val i = x.val j := by
    intro x
    apply hn x.val
    intro j
    have hh := congrFun x.property j
    exact sub_eq_zero.mp hh
  have hinj : Function.Injective (fun x : f.ker =>
      (⟨x.val,hconst x⟩ : {x : Fin k → ZMod 2 // ∀ i j, p.val i j = true → x i = x j})) := by
    intro x y h
    apply Subtype.ext
    exact congrArg (fun z : {x : Fin k → ZMod 2 // ∀ i j, p.val i j = true → x i = x j} => z.val) h
  have hker : Nat.card f.ker ≤ 2^(Blocks p).card := by
    rw [Nat.card_eq_fintype_card]
    exact (Fintype.card_le_of_injective _ hinj).trans_eq (constant_labels_card p)
  have hcard := f.ker.card_mul_index
  rw [AddSubgroup.index_ker] at hcard
  have hrange : Nat.card f.range ≤ 2^e := by
    rw [Nat.card_eq_fintype_card]
    have hh := Fintype.card_subtype_le (p := fun y => y ∈ f.range)
    simpa using hh
  have hwhole : Nat.card (Fin k → ZMod 2) = 2^k := by
    rw [Nat.card_eq_fintype_card,Fintype.card_fun,Fintype.card_fin,ZMod.card]
  rw [hwhole] at hcard
  have hb := Nat.mul_le_mul hker hrange
  rw [hcard,← Nat.pow_add] at hb
  have hpow : 2^(e+(Blocks p).card) < 2^k := Nat.pow_lt_pow_right (by omega) he
  rw [Nat.add_comm] at hpow
  omega

private def LabelPartition {k : ℕ} (x : Fin k → ZMod 2) : Partition k :=
  ⟨fun i j => decide (x i = x j),by
    refine ⟨?_,?_,?_⟩
    · intro i; simp
    · intro i j h; simpa only [decide_eq_true_eq] using (of_decide_eq_true h).symm
    · intro i j l hij hjl
      exact decide_eq_true ((of_decide_eq_true hij).trans (of_decide_eq_true hjl))⟩

private def Generated {k e : ℕ} (u v : Fin e → Fin k) : Partition k :=
  ⟨fun i j => decide (∀ r : Partition k, (∀ s, r.val (u s) (v s) = true) → r.val i j = true),by
    refine ⟨?_,?_,?_⟩
    · intro i
      apply decide_eq_true
      intro r hr
      exact r.property.refl i
    · intro i j h
      apply decide_eq_true
      intro r hr
      exact r.property.symm (of_decide_eq_true h r hr)
    · intro i j l hij hjl
      apply decide_eq_true
      intro r hr
      exact r.property.trans (of_decide_eq_true hij r hr) (of_decide_eq_true hjl r hr)⟩

private lemma generated_constraints {k e : ℕ} (u v : Fin e → Fin k) (s : Fin e) :
    (Generated u v).val (u s) (v s) = true := by
  apply decide_eq_true
  intro r hr
  exact hr s

private lemma generated_le {k e : ℕ} (u v : Fin e → Fin k) (r : Partition k)
    (hr : ∀ s, r.val (u s) (v s) = true) : Refines (Generated u v) r := by
  intro i j hij
  exact of_decide_eq_true hij r hr

private lemma generated_ne {k e : ℕ} (p : Partition k) (u v : Fin e → Fin k)
    (he : e+(Blocks p).card < k) : Generated u v ≠ p := by
  obtain ⟨x,hx,hxp⟩ := sparse_separating_label p u v he
  have hq : ∀ s, (LabelPartition x).val (u s) (v s) = true := by
    intro s
    exact decide_eq_true (hx s)
  intro h
  have hh := generated_le u v (LabelPartition x) hq
  rw [h] at hh
  apply hxp
  intro i j hij
  exact of_decide_eq_true (hh i j hij)

private lemma sparse_mobius_cancel {k e : ℕ} (p : Partition k) (u v : Fin e → Fin k)
    (he : e+(Blocks p).card < k) :
    (∑ r : Partition k, if Refines r p ∧ (∀ s, r.val (u s) (v s) = true) then Mobius r p else 0) = 0 := by
  have hiff (r : Partition k) : (∀ s, r.val (u s) (v s) = true) ↔ Refines (Generated u v) r := by
    constructor
    · exact generated_le u v r
    · intro h s
      exact h _ _ (generated_constraints u v s)
  have hiff' (r : Partition k) : (Refines r p ∧ (∀ s, r.val (u s) (v s) = true)) ↔
      Refines (Generated u v) r ∧ Refines r p := by rw [hiff]; exact and_comm
  simp_rw [hiff']
  by_cases hgp : Refines (Generated u v) p
  · exact partition_mobius_cancellation (Generated u v) p hgp (generated_ne p u v he)
  · apply Finset.sum_eq_zero
    intro r hr
    rw [if_neg]
    rintro ⟨hgr,hrp⟩
    apply hgp
    intro i j hij
    exact hrp i j (hgr i j hij)

private lemma sum_power_expand {k a : ℕ} (S : Finset (Fin k)) (d : Fin k → ℝ) :
    (∑ i ∈ S, d i)^a = ∑ f : Fin a → Fin k,
      if ∀ o, f o ∈ S then ∏ o, d (f o) else 0 := by
  have hs : (∑ i ∈ S, d i) = ∑ i : Fin k, if i ∈ S then d i else 0 :=
    (Finset.sum_ite_mem_eq _ _).symm
  rw [hs,Fintype.sum_pow]
  apply Finset.sum_congr rfl
  intro f hf
  have hh := Fintype.prod_ite_zero (p := fun o : Fin a => f o ∈ S) (f := fun o => d (f o))
  by_cases h : ∀ o, f o ∈ S <;> simpa only [h,if_true,if_false] using hh

private lemma block_membership {k a : ℕ} (ha : 0 < a) (p : Partition k)
    (S : Finset (Fin k)) (hS : S ∈ Blocks p) (f : Fin a → Fin k) :
    (∀ o, f o ∈ S) ↔ S = Class p (f ⟨0,ha⟩) ∧
      (∀ o, p.val (f ⟨0,ha⟩) (f o) = true) := by
  obtain ⟨i,_,rfl⟩ := mem_image.mp hS
  constructor
  · intro hf
    have hi0 := (mem_filter.mp (hf ⟨0,ha⟩)).2
    refine ⟨(class_eq p i _).mpr hi0,?_⟩
    intro o
    exact p.property.trans (p.property.symm hi0) (mem_filter.mp (hf o)).2
  · rintro ⟨heq,hf⟩ o
    rw [heq]
    exact mem_filter.mpr ⟨mem_univ _,hf o⟩

private lemma sum_block_power {k a : ℕ} (ha : 0 < a) (p : Partition k) (d : Fin k → ℝ) :
    (∑ S ∈ Blocks p, (∑ i ∈ S, d i)^a) =
      ∑ f : Fin a → Fin k,
        if ∀ o, p.val (f ⟨0,ha⟩) (f o) = true then ∏ o, d (f o) else 0 := by
  simp_rw [sum_power_expand]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro f hf
  by_cases hc : ∀ o, p.val (f ⟨0,ha⟩) (f o) = true
  · rw [if_pos hc]
    calc
      _ = ∑ S ∈ Blocks p, if S = Class p (f ⟨0,ha⟩) then ∏ o, d (f o) else 0 := by
        apply Finset.sum_congr rfl
        intro S hS
        simp [block_membership ha p S hS f,hc]
      _ = _ := by simp [class_mem]
  · rw [if_neg hc]
    apply Finset.sum_eq_zero
    intro S hS
    rw [if_neg]
    intro hh
    exact hc ((block_membership ha p S hS f).mp hh).2

private def PowerSum {k colors : ℕ} (d : Fin k → Fin colors → ℝ) (a : ℕ) (p : Partition k) : ℝ :=
  ∑ S ∈ Blocks p, ∑ j : Fin colors, (∑ i ∈ S, d i j)^a

private lemma powerSum_expand {k colors a : ℕ} (ha : 0 < a)
    (d : Fin k → Fin colors → ℝ) (p : Partition k) :
    PowerSum d a p = ∑ z : Fin colors × (Fin a → Fin k),
      if ∀ o, p.val (z.2 ⟨0,ha⟩) (z.2 o) = true then ∏ o, d (z.2 o) z.1 else 0 := by
  unfold PowerSum
  rw [Finset.sum_comm]
  simp_rw [sum_block_power ha]
  exact (Finset.sum_product (univ : Finset (Fin colors)) (univ : Finset (Fin a → Fin k))
    (fun z : Fin colors × (Fin a → Fin k) =>
      if ∀ o, p.val (z.2 ⟨0,ha⟩) (z.2 o) = true then ∏ o, d (z.2 o) z.1 else (0:ℝ))).symm

private lemma sparse_cancel_type {k : ℕ} {E : Type*} [Fintype E]
    (p : Partition k) (u v : E → Fin k) (he : Fintype.card E+(Blocks p).card < k) :
    (∑ r : Partition k, if Refines r p ∧ (∀ s, r.val (u s) (v s) = true) then Mobius r p else 0) = 0 := by
  let eqv := Fintype.equivFin E
  have hh := sparse_mobius_cancel p (u ∘ eqv.symm) (v ∘ eqv.symm) he
  have hiff (r : Partition k) : (∀ s : Fin (Fintype.card E), r.val (u (eqv.symm s)) (v (eqv.symm s)) = true) ↔
      (∀ s : E, r.val (u s) (v s) = true) := by
    constructor
    · intro h s
      simpa using h (eqv s)
    · intro h s
      exact h (eqv.symm s)
  simpa only [Function.comp_apply,hiff] using hh

private abbrev Assignments (k colors m : ℕ) (a : Fin m → ℕ) :=
  ∀ t : Fin m, Fin colors × (Fin (a t) → Fin k)

private lemma productPower_expand {k colors m : ℕ} (a : Fin m → ℕ) (ha : ∀ t, 0 < a t)
    (d : Fin k → Fin colors → ℝ) (r : Partition k) :
    (∏ t : Fin m, PowerSum d (a t) r) =
      ∑ f : Assignments k colors m a,
        if ∀ t o, r.val ((f t).2 ⟨0,ha t⟩) ((f t).2 o) = true then
          ∏ t, ∏ o, d ((f t).2 o) (f t).1 else 0 := by
  have heq (t : Fin m) := powerSum_expand (ha t) d r
  simp_rw [heq]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro f hf
  have hh := Fintype.prod_ite_zero
    (p := fun t : Fin m => ∀ o, r.val ((f t).2 ⟨0,ha t⟩) ((f t).2 o) = true)
    (f := fun t => ∏ o, d ((f t).2 o) (f t).1)
  by_cases h : ∀ t o, r.val ((f t).2 ⟨0,ha t⟩) ((f t).2 o) = true <;>
    simpa only [h,if_true,if_false] using hh

private lemma power_mobius_cancel {k colors m : ℕ} (p : Partition k)
    (a : Fin m → ℕ) (ha : ∀ t, 0 < a t) (d : Fin k → Fin colors → ℝ)
    (hbudget : (∑ t, (a t-1))+(Blocks p).card < k) :
    (∑ r : Partition k, if Refines r p then
      (Mobius r p:ℝ)*(∏ t : Fin m, PowerSum d (a t) r) else 0) = 0 := by
  let E := (t : Fin m) × Fin (a t-1)
  have hE : Fintype.card E+(Blocks p).card < k := by
    simpa only [E,Fintype.card_sigma,Fintype.card_fin] using hbudget
  have hterm (r : Partition k) :
      (if Refines r p then (Mobius r p:ℝ)*(∏ t : Fin m, PowerSum d (a t) r) else 0) =
      ∑ f : Assignments k colors m a,
        (if Refines r p ∧ (∀ t o, r.val ((f t).2 ⟨0,ha t⟩) ((f t).2 o) = true) then
          (Mobius r p:ℝ) else 0) * (∏ t, ∏ o, d ((f t).2 o) (f t).1) := by
    rw [productPower_expand a ha d r]
    by_cases hr : Refines r p
    · simp only [hr,if_true,true_and,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro f hf
      split_ifs <;> simp
    · simp [hr]
  simp_rw [hterm]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro f hf
  let u : E → Fin k := fun s => (f s.1).2 ⟨0,ha s.1⟩
  let v : E → Fin k := fun s => (f s.1).2 ⟨s.2.val+1,by have h := s.2.isLt; have h0 := ha s.1; omega⟩
  have hiff (r : Partition k) :
      (∀ t o, r.val ((f t).2 ⟨0,ha t⟩) ((f t).2 o) = true) ↔
      (∀ s : E, r.val (u s) (v s) = true) := by
    constructor
    · intro h s
      exact h s.1 _
    · intro h t o
      by_cases ho : o.val = 0
      · have heq : o = ⟨0,ha t⟩ := Fin.ext ho
        rw [heq]
        exact r.property.refl _
      · let s : E := ⟨t,⟨o.val-1,by have h0 := ha t; have ho' := o.isLt; omega⟩⟩
        have hh := h s
        have heq : (⟨(s.2.val)+1,by have h0 := ha s.1; have hs := s.2.isLt; omega⟩ : Fin (a s.1)) = o := by
          apply Fin.ext
          dsimp [s]
          omega
        simpa only [u,v,heq] using hh
  simp_rw [hiff]
  rw [← Finset.sum_mul]
  have hz := congrArg (fun x : ℤ => (x:ℝ)) (sparse_cancel_type p u v hE)
  push_cast at hz
  rw [hz,zero_mul]

end
end QuantumBipartiteTesting.Bipartiteness.PowerProof

open QuantumBipartiteTesting.Bipartiteness
open QuantumBipartiteTesting.Bipartiteness.PowerProof
open scoped BigOperators Classical

theorem solution {k colors m : ℕ} (p : Partition k) (a : Fin m → ℕ)
    (ha : ∀ t, 0 < a t) (d : Fin k → Fin colors → ℝ)
    (hbudget : (∑ t, (a t-1))+(Blocks p).card < k) :
    (∑ r : Partition k, if Refines r p then (Mobius r p:ℝ) *
      (∏ t : Fin m, ∑ S ∈ Blocks r, ∑ j : Fin colors, (∑ i ∈ S, d i j)^(a t)) else 0) = 0 := by
  exact power_mobius_cancel p a ha d hbudget
