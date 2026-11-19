-- Prove2me | solution 1 for QuantumBipartiteTesting.Bipartiteness.topology_pattern_comparison
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T15:25:24.079833+00:00
-- url     : https://prove2.me/submissions/daded521-59f3-4134-9faa-430ef5c8d2a3

import Definitions.Def_QuantumBipartiteTesting_Bipartiteness_Reduction
import Theorems.Thm_QuantumBipartiteTesting_Bipartiteness_partition_mobius_cancellation
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Theorems.Thm_QuantumBipartiteTesting_Bipartiteness_uniform_block_matching_contains

namespace QuantumBipartiteTesting.Bipartiteness.SamplingProof
noncomputable section
open Finset
attribute [local instance] Classical.propDecidable Classical.decEq
set_option maxHeartbeats 500000
set_option maxRecDepth 2000
set_option backward.isDefEq.respectTransparency.types false

private lemma average_bounds {α : Type*} (s : Finset α) (f : α → ℝ)
    (hf : ∀ x ∈ s, 0 ≤ f x ∧ f x ≤ 1) : 0 ≤ Average s f ∧ Average s f ≤ 1 := by
  unfold Average
  constructor
  · exact div_nonneg (sum_nonneg (fun x hx => (hf x hx).1)) (Nat.cast_nonneg _)
  · by_cases hs : s.card = 0
    · simp [hs]
    · apply (div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hs)).mpr
      calc
        _ ≤ ∑ x ∈ s, (1:ℝ) := sum_le_sum (fun x hx => (hf x hx).2)
        _ = _ := by simp

private lemma sum_eq_card_mul_average {α : Type*} (s : Finset α) (f : α → ℝ) :
    (∑ x ∈ s, f x) = (s.card:ℝ)*Average s f := by
  by_cases hs : s.card = 0
  · have he : s = ∅ := card_eq_zero.mp hs
    simp [he,Average]
  · unfold Average
    field_simp

private lemma conditioning_error {α : Type*} (s t : Finset α) (f : α → ℝ)
    (hts : t ⊆ s) (hf : ∀ x ∈ s, 0 ≤ f x ∧ f x ≤ 1) :
    |Average t f - Average s f| ≤ Average s (fun x => if x ∈ t then (0:ℝ) else 1) := by
  have hbS := average_bounds s f hf
  have hbT := average_bounds t f (fun x hx => hf x (hts hx))
  have hbU := average_bounds (s\t) f (fun x hx => hf x (mem_sdiff.mp hx).1)
  by_cases ht : t.Nonempty
  swap
  · have he : t = ∅ := not_nonempty_iff_eq_empty.mp ht
    subst t
    by_cases hs : s.Nonempty
    · have hspos : (0:ℝ) < s.card := by exact_mod_cast hs.card_pos
      have hab : |Average s f| ≤ 1 := by rw [abs_of_nonneg hbS.1]; exact hbS.2
      simpa [Average,hspos.ne'] using hab
    · have he : s = ∅ := not_nonempty_iff_eq_empty.mp hs
      simp [he,Average]
  have hspos : (0:ℝ) < s.card := by exact_mod_cast (ht.mono hts).card_pos
  have hcount : (s.card:ℝ) = (t.card:ℝ)+(s\t).card := by
    exact_mod_cast (card_sdiff_add_card_eq_card hts).symm.trans (Nat.add_comm _ _)
  have hsum : (∑ x ∈ s, f x) = (∑ x ∈ t, f x)+(∑ x ∈ s\t, f x) := by
    rw [add_comm,Finset.sum_sdiff hts]
  have hweight : Average s f =
      ((t.card:ℝ)*Average t f+(s\t).card*Average (s\t) f)/(s.card:ℝ) := by
    conv_lhs => unfold Average
    rw [hsum,sum_eq_card_mul_average t f,sum_eq_card_mul_average (s\t) f]
  have hdelta : Average s (fun x => if x ∈ t then (0:ℝ) else 1) =
      ((s\t).card:ℝ)/(s.card:ℝ) := by
    unfold Average
    congr 1
    have heq : (∑ x ∈ s, (fun x => if x ∈ t then (0:ℝ) else 1) x) =
        ∑ x ∈ s.filter (fun x => x ∉ t), (1:ℝ) := by
      rw [Finset.sum_filter]
      apply sum_congr rfl
      intro x hx
      by_cases h : x ∈ t <;> simp [h]
    rw [heq]
    have hfilter : s.filter (fun x => x ∉ t) = s\t := by ext x; simp
    rw [hfilter]
    simp
  rw [hweight,hdelta]
  have hid : Average t f -
      ((t.card:ℝ)*Average t f+(s\t).card*Average (s\t) f)/(s.card:ℝ) =
      ((s\t).card:ℝ)/(s.card:ℝ)*(Average t f-Average (s\t) f) := by
    field_simp
    rw [hcount]
    ring
  rw [hid,abs_mul,abs_of_nonneg (by positivity)]
  have hab : |Average t f-Average (s\t) f| ≤ 1 := abs_le.mpr ⟨by linarith,by linarith⟩
  exact (mul_le_mul_of_nonneg_left hab (by positivity)).trans_eq (mul_one _)

private lemma coordinate_div {l s : ℕ} (j : Fin l) (x : Fin s) :
    (finProdFinEquiv (j,x)).val/s = j.val := by
  exact congrArg (fun p : Fin l × Fin s => p.1.val) (finProdFinEquiv.symm_apply_apply (j,x))

private lemma embeddings_nonempty {N l s : ℕ} (hl : 0 < l) (b : Fin N → Fin l)
    (hcap : ∀ j, (univ.filter (fun v => b v = j)).card ≤ s) :
    (Embeddings (l*s) b).Nonempty := by
  have hemb (j : Fin l) : Nonempty ({v : Fin N // b v = j} ↪ Fin s) := by
    apply Function.Embedding.nonempty_iff_card_le.mpr
    simpa only [Fintype.card_subtype,Fintype.card_fin] using hcap j
  let f := fun j => Classical.choice (hemb j)
  let t := fun v : Fin N => finProdFinEquiv (b v,f (b v) ⟨v,rfl⟩)
  have ht : Function.Injective t := by
    intro u v h
    have hp := finProdFinEquiv.injective h
    have hb := congrArg Prod.fst hp
    have hs := congrArg Prod.snd hp
    have htransport (j : Fin l) (h : b v = j) : f (b v) ⟨v,rfl⟩ = f j ⟨v,h⟩ := by
      subst j
      rfl
    have hrw := htransport (b u) hb.symm
    exact congrArg Subtype.val ((f (b u)).injective (hs.trans hrw))
  refine ⟨t,mem_filter.mpr ⟨mem_univ _,ht,?_⟩⟩
  intro v
  rw [Nat.mul_div_cancel_left s hl]
  exact coordinate_div (b v) (f (b v) ⟨v,rfl⟩)

private lemma noOverflow_nonempty {N l s : ℕ} (hl : 0 < l) (hN : N ≤ l*s) :
    (univ.filter (NoOverflow N (l*s) l)).Nonempty := by
  let t : Fin N → Fin (l*s) := Fin.castLE hN
  let b := fun v => (finProdFinEquiv.symm (t v) : Fin l × Fin s).1
  refine ⟨b,mem_filter.mpr ⟨mem_univ _,?_⟩⟩
  intro j
  rw [Nat.mul_div_cancel_left s hl]
  have hf : Function.Injective (fun v : {v : Fin N // b v = j} =>
      (finProdFinEquiv.symm (t v.val) : Fin l × Fin s).2) := by
    intro u v h
    apply Subtype.ext
    apply Fin.castLE_injective hN
    apply finProdFinEquiv.symm.injective
    exact Prod.ext (u.property.trans v.property.symm) h
  have hh := Fintype.card_le_of_injective _ hf
  simpa only [Fintype.card_subtype,Fintype.card_fin] using hh

private lemma matchings_nonempty (l s : ℕ) (hl : 0 < l) (hs : Even s) :
    (Matchings (l*s) l).Nonempty := by
  by_contra h
  have he : Matchings (l*s) l = ∅ := not_nonempty_iff_eq_empty.mp h
  have hh := uniform_block_matching_contains l s hl hs (fun _ => ∅)
    (by simp) (by simp)
  simp only [he,Average,sum_empty,card_empty,Nat.cast_zero,zero_div,card_empty,prod_range_zero,prod_const_one] at hh
  norm_num at hh

private lemma partition_le_iff {k : ℕ} (p r : Partition k) : p ≤ r ↔ Refines p r := by
  change (∀ i j, p.val i j ≤ r.val i j) ↔ (∀ i j, p.val i j = true → r.val i j = true)
  simp only [Bool.le_iff_imp]

private lemma refines_refl {k : ℕ} (p : Partition k) : Refines p p := fun _ _ h => h

private lemma refines_trans {k : ℕ} {p r s : Partition k} (hpr : Refines p r) (hrs : Refines r s) : Refines p s :=
  fun i j h => hrs i j (hpr i j h)

private lemma refines_antisymm {k : ℕ} {p r : Partition k} (hpr : Refines p r) (hrp : Refines r p) : p = r :=
  le_antisymm ((partition_le_iff _ _).mpr hpr) ((partition_le_iff _ _).mpr hrp)

private lemma mobius_zero {k : ℕ} (p r : Partition k) (h : ¬ Refines p r) : Mobius p r = 0 := by
  have hne : p ≠ r := by rintro rfl; exact h (refines_refl p)
  simp [Mobius,hne,h]

private lemma mobius_upper_all {k : ℕ} (p r : Partition k) :
    (∑ t : Partition k, if Refines p t ∧ Refines t r then Mobius t r else 0) =
      if p = r then 1 else 0 := by
  by_cases heq : p = r
  · subst r
    rw [if_pos rfl,Finset.sum_eq_single p]
    · simp [refines_refl,Mobius]
    · intro t ht htp
      have hn : ¬ (Refines p t ∧ Refines t p) := fun h => htp (refines_antisymm h.2 h.1)
      simp [hn]
    · simp
  · rw [if_neg heq]
    by_cases h : Refines p r
    · exact partition_mobius_cancellation p r h heq
    · apply Finset.sum_eq_zero
      intro t ht
      have hn : ¬ (Refines p t ∧ Refines t r) := fun hh => h (refines_trans hh.1 hh.2)
      simp [hn]

private def Zeta (k : ℕ) : Matrix (Partition k) (Partition k) ℤ :=
  fun p r => if Refines p r then 1 else 0
private def Mu (k : ℕ) : Matrix (Partition k) (Partition k) ℤ := fun p r => Mobius p r

private lemma zeta_mul_mu (k : ℕ) : Zeta k * Mu k = 1 := by
  ext p r
  simp only [Matrix.mul_apply,Zeta,Mu,ite_mul,one_mul,zero_mul]
  have heq : (∑ t : Partition k, if Refines p t then Mobius t r else 0) =
      ∑ t : Partition k, if Refines p t ∧ Refines t r then Mobius t r else 0 := by
    apply sum_congr rfl
    intro t ht
    by_cases hpt : Refines p t <;> by_cases htr : Refines t r <;>
      simp [hpt,htr] <;> exact mobius_zero t r htr
  rw [heq,mobius_upper_all,Matrix.one_apply]

private lemma mu_mul_zeta (k : ℕ) : Mu k * Zeta k = 1 :=
  mul_eq_one_comm.mp (zeta_mul_mu k)

private lemma mobius_lower_all {k : ℕ} (p r : Partition k) :
    (∑ t : Partition k, if Refines p t ∧ Refines t r then Mobius p t else 0) =
      if p = r then 1 else 0 := by
  have hh := congrFun (congrFun (mu_mul_zeta k) p) r
  simp only [Matrix.mul_apply,Zeta,Mu,mul_ite,mul_one,mul_zero,Matrix.one_apply] at hh
  rw [← hh]
  apply sum_congr rfl
  intro t ht
  by_cases hpt : Refines p t <;> by_cases htr : Refines t r <;>
    simp [hpt,htr] <;> exact (mobius_zero p t hpt).symm

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

private def labelEquiv {k l : ℕ} (p : Partition k) :
    (Quotient (PSetoid p) → Fin l) ≃
      {x : Fin k → Fin l // ∀ i j, p.val i j = true → x i = x j} where
  toFun f := ⟨fun i => f (Quotient.mk (PSetoid p) i),
    fun i j hij => congrArg f (Quotient.sound hij)⟩
  invFun x := fun q => Quotient.liftOn q x.val x.property
  left_inv f := by
    funext q
    induction q using Quotient.inductionOn with
    | h i => rfl
  right_inv x := by apply Subtype.ext; rfl

private lemma constant_labels_card {k l : ℕ} (p : Partition k) :
    Fintype.card {x : Fin k → Fin l // ∀ i j, p.val i j = true → x i = x j} =
      l^(Blocks p).card := by
  rw [← Fintype.card_congr (labelEquiv p),Fintype.card_fun,Fintype.card_fin]
  have hh : Fintype.card (Quotient (PSetoid p)) = (Blocks p).card := by
    rw [Fintype.card_congr (blockEquiv p),Fintype.card_coe]
  rw [hh]


private def Kernel {k l : ℕ} (x : Fin k → Fin l) : Partition k :=
  ⟨fun i j => decide (x i = x j), by
    refine ⟨?_,?_,?_⟩
    · intro i; simp
    · intro i j h; simp only [decide_eq_true_eq] at h ⊢; exact h.symm
    · intro i j m h₁ h₂; simp only [decide_eq_true_eq] at h₁ h₂ ⊢; exact h₁.trans h₂⟩

private lemma constant_labels_mass {k l : ℕ} (p : Partition k) :
    (l:ℝ)^(Blocks p).card =
      ∑ x : Fin k → Fin l, if Refines p (Kernel x) then (1:ℝ) else 0 := by
  have hh := constant_labels_card (l := l) p
  rw [Fintype.card_subtype] at hh
  have heq : (univ.filter (fun x : Fin k → Fin l => ∀ i j, p.val i j = true → x i = x j)) =
      univ.filter (fun x : Fin k → Fin l => Refines p (Kernel x)) := by
    ext x
    simp only [mem_filter,mem_univ,true_and,Refines,Kernel,decide_eq_true_eq]
  rw [heq] at hh
  rw [← Nat.cast_pow,← hh]
  rw [Finset.card_eq_sum_ones]
  push_cast
  rw [Finset.sum_filter]

private lemma kernel_partition_count {k l : ℕ} (p : Partition k) :
    (∑ r : Partition k, if Refines p r then (Mobius p r:ℝ)*(l:ℝ)^(Blocks r).card else 0) =
      ((univ.filter (fun x : Fin k → Fin l => Kernel x = p)).card:ℝ) := by
  simp_rw [constant_labels_mass]
  simp only [Finset.mul_sum]
  have heq (r : Partition k) :
      (if Refines p r then ∑ x : Fin k → Fin l, (Mobius p r:ℝ)*(if Refines r (Kernel x) then 1 else 0) else 0) =
      ∑ x : Fin k → Fin l, if Refines p r then (Mobius p r:ℝ)*(if Refines r (Kernel x) then 1 else 0) else 0 := by
    by_cases h : Refines p r <;> simp [h]
  simp_rw [heq]
  rw [Finset.sum_comm]
  rw [Finset.card_eq_sum_ones]
  push_cast
  rw [Finset.sum_filter]
  apply sum_congr rfl
  intro x hx
  have hh := mobius_lower_all p (Kernel x)
  have hr := congrArg (fun z : ℤ => (z:ℝ)) hh
  push_cast at hr
  convert hr using 1
  · apply sum_congr rfl
    intro r hr
    by_cases hpr : Refines p r <;> by_cases hxr : Refines r (Kernel x) <;> simp [hpr,hxr]
  · by_cases h : p = Kernel x <;> simp [h,eq_comm]

private lemma adj_symm {N c : ℕ} (F : Finset (ColoredEdge N c)) : Symmetric (Adj F) := by
  intro u v h
  obtain ⟨e, he, h | h⟩ := h
  · exact ⟨e, he, Or.inr h⟩
  · exact ⟨e, he, Or.inl h⟩

private lemma reach_symm {N c : ℕ} (F : Finset (ColoredEdge N c)) {u v : Fin N}
    (h : Relation.ReflTransGen (Adj F) u v) : Relation.ReflTransGen (Adj F) v u := by
  induction h with
  | refl => exact .refl
  | tail h hvw ih => exact (Relation.ReflTransGen.single (adj_symm F hvw)).trans ih

private def reachSetoid {N c : ℕ} (F : Finset (ColoredEdge N c)) : Setoid (Fin N) where
  r := Relation.ReflTransGen (Adj F)
  iseqv := ⟨fun _ => .refl, fun h => reach_symm F h, fun h h' => h.trans h'⟩

private def fullClass {N c : ℕ} (F : Finset (ColoredEdge N c)) (u : Fin N) : Finset (Fin N) :=
  univ.filter fun v => Relation.ReflTransGen (Adj F) u v

private lemma mem_fullClass {N c : ℕ} (F : Finset (ColoredEdge N c)) (u v : Fin N) :
    v ∈ fullClass F u ↔ Relation.ReflTransGen (Adj F) u v := by
  simp [fullClass]

private lemma self_fullClass {N c : ℕ} (F : Finset (ColoredEdge N c)) (u : Fin N) :
    u ∈ fullClass F u := (mem_fullClass F u u).mpr .refl

private lemma fullClass_eq_iff {N c : ℕ} (F : Finset (ColoredEdge N c)) (u v : Fin N) :
    fullClass F u = fullClass F v ↔ Relation.ReflTransGen (Adj F) u v := by
  constructor
  · intro h
    rw [← mem_fullClass F u v, h]
    exact self_fullClass F v
  · intro h
    ext w
    simp only [mem_fullClass]
    exact ⟨fun hw => (reach_symm F h).trans hw, fun hw => h.trans hw⟩

private lemma adj_incident {N c : ℕ} (F : Finset (ColoredEdge N c)) {u v : Fin N}
    (h : Adj F u v) : u ∈ Vertices F ∧ v ∈ Vertices F := by
  obtain ⟨e, he, h | h⟩ := h
  · exact ⟨by simp only [Vertices, mem_filter, mem_univ, true_and]; exact ⟨e,he,Or.inl h.1⟩,
      by simp only [Vertices, mem_filter, mem_univ, true_and]; exact ⟨e,he,Or.inr h.2⟩⟩
  · exact ⟨by simp only [Vertices, mem_filter, mem_univ, true_and]; exact ⟨e,he,Or.inr h.2⟩,
      by simp only [Vertices, mem_filter, mem_univ, true_and]; exact ⟨e,he,Or.inl h.1⟩⟩

private lemma reach_incident {N c : ℕ} (F : Finset (ColoredEdge N c)) {u v : Fin N}
    (hu : u ∈ Vertices F) (h : Relation.ReflTransGen (Adj F) u v) : v ∈ Vertices F := by
  induction h with
  | refl => exact hu
  | @tail v w h hvw ih => exact (adj_incident F hvw).2

private lemma isolated_class {N c : ℕ} (F : Finset (ColoredEdge N c)) {u : Fin N}
    (hu : u ∉ Vertices F) : fullClass F u = {u} := by
  ext v
  simp only [mem_fullClass, mem_singleton]
  constructor
  · intro h
    induction h with
    | refl => rfl
    | @tail v w h hvw ih => exact (hu (ih ▸ (adj_incident F hvw).1)).elim
  · rintro rfl
    exact .refl

private lemma component_fullClass {N c : ℕ} (F : Finset (ColoredEdge N c)) {u : Fin N}
    (hu : u ∈ Vertices F) :
    (Vertices F).filter (fun v => Relation.ReflTransGen (Adj F) u v) = fullClass F u := by
  ext v
  simp only [mem_filter, mem_fullClass]
  exact ⟨And.right, fun h => ⟨reach_incident F hu h, h⟩⟩


private lemma componentAt_eq {N colors : ℕ} (F : Finset (ColoredEdge N colors))
    (i : Fin (Components F).card) :
    ComponentAt F i = (Components F).toList[i.val]'(by simpa using i.isLt) := by
  have hi : i.val < (Components F).toList.length := by simpa only [length_toList] using i.isLt
  unfold ComponentAt
  rw [List.getElem?_eq_getElem hi]
  rfl

private lemma componentAt_mem {N colors : ℕ} (F : Finset (ColoredEdge N colors))
    (i : Fin (Components F).card) : ComponentAt F i ∈ Components F := by
  rw [componentAt_eq]
  exact mem_toList.mp (List.getElem_mem _)

private lemma componentAt_injective {N colors : ℕ} (F : Finset (ColoredEdge N colors)) :
    Function.Injective (ComponentAt F) := by
  intro i j h
  simp only [componentAt_eq] at h
  exact Fin.ext ((Components F).nodup_toList.getElem_inj_iff.mp h)

private lemma componentAt_surjective {N colors : ℕ} (F : Finset (ColoredEdge N colors))
    (S : Finset (Fin N)) (hS : S ∈ Components F) : ∃ i, ComponentAt F i = S := by
  obtain ⟨i,hi,he⟩ := List.getElem_of_mem (mem_toList.mpr hS)
  refine ⟨⟨i,by simpa using hi⟩,?_⟩
  rw [componentAt_eq]
  exact he

private lemma sum_componentAt {N colors : ℕ} (F : Finset (ColoredEdge N colors))
    (f : Finset (Fin N) → ℕ) :
    (∑ i : Fin (Components F).card, f (ComponentAt F i)) = ∑ S ∈ Components F, f S := by
  apply Finset.sum_bij (fun i _ => ComponentAt F i)
  · intro i hi; exact componentAt_mem F i
  · intro i hi j hj hij; exact componentAt_injective F hij
  · intro S hS; obtain ⟨i,hi⟩ := componentAt_surjective F S hS; exact ⟨i,mem_univ _,hi⟩
  · intros; rfl

private lemma component_containing {N colors : ℕ} (F : Finset (ColoredEdge N colors))
    (u : Fin N) (hu : u ∈ Vertices F) (S : Finset (Fin N)) (hS : S ∈ Components F) :
    u ∈ S ↔ S = fullClass F u := by
  obtain ⟨v,hv,rfl⟩ := mem_image.mp hS
  rw [component_fullClass F hv,mem_fullClass]
  constructor
  · intro h; exact (fullClass_eq_iff F v u).mpr h
  · intro h; exact (fullClass_eq_iff F v u).mp h


private lemma component_subset {N colors : ℕ} (F : Finset (ColoredEdge N colors))
    {S : Finset (Fin N)} (hS : S ∈ Components F) : S ⊆ Vertices F := by
  obtain ⟨u,hu,rfl⟩ := mem_image.mp hS
  exact filter_subset _ _

private lemma component_nonempty {N colors : ℕ} (F : Finset (ColoredEdge N colors))
    (i : Fin (Components F).card) : (ComponentAt F i).Nonempty := by
  obtain ⟨u,hu,he⟩ := mem_image.mp (componentAt_mem F i)
  refine ⟨u,?_⟩
  rw [← he]
  exact mem_filter.mpr ⟨hu,Relation.ReflTransGen.refl⟩

private lemma vertex_component_exists {N colors : ℕ} (F : Finset (ColoredEdge N colors))
    (v : {v // v ∈ Vertices F}) : ∃ i, v.val ∈ ComponentAt F i := by
  have hc : fullClass F v.val ∈ Components F :=
    mem_image.mpr ⟨v.val,v.property,component_fullClass F v.property⟩
  obtain ⟨i,hi⟩ := componentAt_surjective F _ hc
  exact ⟨i,hi.symm ▸ self_fullClass F v.val⟩

private def CompIndex {N colors : ℕ} (F : Finset (ColoredEdge N colors))
    (v : {v // v ∈ Vertices F}) : Fin (Components F).card :=
  (vertex_component_exists F v).choose

private lemma index_mem {N colors : ℕ} (F : Finset (ColoredEdge N colors))
    (v : {v // v ∈ Vertices F}) : v.val ∈ ComponentAt F (CompIndex F v) :=
  (vertex_component_exists F v).choose_spec

private lemma index_unique {N colors : ℕ} (F : Finset (ColoredEdge N colors))
    (v : {v // v ∈ Vertices F}) (i : Fin (Components F).card) (hi : v.val ∈ ComponentAt F i) :
    CompIndex F v = i := by
  apply componentAt_injective F
  rw [(component_containing F v.val v.property _ (componentAt_mem F _)).mp (index_mem F v),
    (component_containing F v.val v.property _ (componentAt_mem F i)).mp hi]

private def CompRep {N colors : ℕ} (F : Finset (ColoredEdge N colors))
    (i : Fin (Components F).card) : {v // v ∈ Vertices F} :=
  ⟨(component_nonempty F i).choose,
    component_subset F (componentAt_mem F i) (component_nonempty F i).choose_spec⟩

private lemma rep_mem {N colors : ℕ} (F : Finset (ColoredEdge N colors))
    (i : Fin (Components F).card) : (CompRep F i).val ∈ ComponentAt F i :=
  (component_nonempty F i).choose_spec

private lemma index_rep {N colors : ℕ} (F : Finset (ColoredEdge N colors))
    (i : Fin (Components F).card) : CompIndex F (CompRep F i) = i :=
  index_unique F _ i (rep_mem F i)

private def EdgeConstant {N colors l : ℕ} (F : Finset (ColoredEdge N colors)) (b : Fin N → Fin l) : Prop :=
  ∀ e ∈ F, b e.1 = b e.2.1

private lemma reach_constant {N colors l : ℕ} (F : Finset (ColoredEdge N colors)) (b : Fin N → Fin l)
    (hb : EdgeConstant F b) {u v : Fin N} (huv : Relation.ReflTransGen (Adj F) u v) : b u = b v := by
  induction huv with
  | refl => rfl
  | @tail v w huv hvw ih =>
    obtain ⟨e,he,h | h⟩ := hvw
    · exact ih.trans (by simpa only [← h.1,← h.2] using hb e he)
    · exact ih.trans (by simpa only [← h.1,← h.2] using (hb e he).symm)

private lemma component_constant {N colors l : ℕ} (F : Finset (ColoredEdge N colors)) (b : Fin N → Fin l)
    (hb : EdgeConstant F b) (i : Fin (Components F).card) {u v : Fin N}
    (hu : u ∈ ComponentAt F i) (hv : v ∈ ComponentAt F i) : b u = b v := by
  obtain ⟨w,hw,hS⟩ := mem_image.mp (componentAt_mem F i)
  rw [← hS] at hu hv
  exact reach_constant F b hb ((reach_symm F (mem_filter.mp hu).2).trans (mem_filter.mp hv).2)

private lemma vertex_rep_value {N colors l : ℕ} (F : Finset (ColoredEdge N colors)) (b : Fin N → Fin l)
    (hb : EdgeConstant F b) (v : {v // v ∈ Vertices F}) : b v.val = b (CompRep F (CompIndex F v)).val :=
  component_constant F b hb _ (index_mem F v) (rep_mem F _)

private lemma endpoints_mem {N colors : ℕ} (F : Finset (ColoredEdge N colors))
    (e : ColoredEdge N colors) (he : e ∈ F) : e.1 ∈ Vertices F ∧ e.2.1 ∈ Vertices F := by
  constructor
  · exact mem_filter.mpr ⟨mem_univ _,e,he,Or.inl rfl⟩
  · exact mem_filter.mpr ⟨mem_univ _,e,he,Or.inr rfl⟩

private lemma edge_indices {N colors : ℕ} (F : Finset (ColoredEdge N colors))
    (e : ColoredEdge N colors) (he : e ∈ F) :
    CompIndex F ⟨e.1,(endpoints_mem F e he).1⟩ = CompIndex F ⟨e.2.1,(endpoints_mem F e he).2⟩ := by
  let u : {v // v ∈ Vertices F} := ⟨e.1,(endpoints_mem F e he).1⟩
  let v : {v // v ∈ Vertices F} := ⟨e.2.1,(endpoints_mem F e he).2⟩
  have hc : ComponentAt F (CompIndex F u) = fullClass F e.1 :=
    (component_containing F e.1 u.property _ (componentAt_mem F _)).mp (index_mem F u)
  have hv : v.val ∈ ComponentAt F (CompIndex F u) := by
    rw [hc,mem_fullClass]
    exact Relation.ReflTransGen.single ⟨e,he,Or.inl ⟨rfl,rfl⟩⟩
  exact (index_unique F v _ hv).symm

private def componentLabelEquiv {N colors l : ℕ} (F : Finset (ColoredEdge N colors)) :
    {b : Fin N → Fin l // EdgeConstant F b} ≃
      ((Fin (Components F).card → Fin l) × ({v // v ∉ Vertices F} → Fin l)) where
  toFun b := (fun i => b.val (CompRep F i).val,fun v => b.val v.val)
  invFun x := ⟨fun v => if h : v ∈ Vertices F then x.1 (CompIndex F ⟨v,h⟩) else x.2 ⟨v,h⟩,by
    intro e he
    dsimp only
    rw [dif_pos (endpoints_mem F e he).1,dif_pos (endpoints_mem F e he).2,edge_indices F e he]⟩
  left_inv b := by
    apply Subtype.ext
    funext v
    dsimp only
    by_cases h : v ∈ Vertices F
    · rw [dif_pos h]
      exact (vertex_rep_value F b.val b.property ⟨v,h⟩).symm
    · rw [dif_neg h]
  right_inv x := by
    apply Prod.ext
    · funext i
      dsimp only
      rw [dif_pos (CompRep F i).property,index_rep]
    · funext v
      dsimp only
      rw [dif_neg v.property]

private def CountMoment {k colors : ℕ} (d : Fin k → Fin colors → ℕ) (p : Partition k) (M l : ℝ) : ℝ :=
  ∏ S ∈ Blocks p, ∏ j : Fin colors, MatchingMoment (∑ i ∈ S, d i j) M l

private lemma kernel_moment {k colors l : ℕ} (d : Fin k → Fin colors → ℕ) (x : Fin k → Fin l)
    (M a : ℝ) : CountMoment d (Kernel x) M a =
      ∏ j : Fin l, ∏ c : Fin colors, MatchingMoment (∑ i ∈ univ.filter (fun i => x i = j), d i c) M a := by
  let Fib := fun j : Fin l => univ.filter (fun i => x i = j)
  have hclass (i : Fin k) : (univ.filter (fun j => (Kernel x).val i j = true)) = Fib (x i) := by
    ext j
    simp only [Kernel,Fib,mem_filter,mem_univ,true_and,decide_eq_true_eq]
    exact eq_comm
  have hK : Blocks (Kernel x) = (univ.image x).image Fib := by
    simp only [Blocks,hclass,Finset.image_image]
    rfl
  have hfib : Set.InjOn Fib (univ.image x) := by
    intro j hj j' hj' heq
    obtain ⟨i,hi,hij⟩ := mem_image.mp hj
    have hmem : i ∈ Fib j := mem_filter.mpr ⟨mem_univ _,hij⟩
    rw [heq] at hmem
    exact hij.symm.trans (mem_filter.mp hmem).2
  unfold CountMoment
  rw [hK,Finset.prod_image hfib]
  apply Finset.prod_subset (subset_univ _)
  intro j hj hnot
  have hFib : Fib j = ∅ := by
    apply filter_eq_empty_iff.mpr
    intro i hi hij
    exact hnot (mem_image.mpr ⟨i,mem_univ _,hij⟩)
  change (∏ c : Fin colors, MatchingMoment (∑ i ∈ Fib j, d i c) M a) = 1
  simp only [hFib,sum_empty,MatchingMoment,range_zero,prod_empty,prod_const_one]

private lemma sum_if_subtype {α : Type*} [Fintype α] (P : α → Prop) (f : α → ℝ) :
    (∑ x : α, if P x then f x else 0) = ∑ x : {x // P x}, f x.val := by
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun x hx => (⟨x,(mem_filter.mp hx).2⟩ : {x // P x}))
  · intro x hx; exact mem_univ _
  · intro x hx y hy hxy; exact congrArg Subtype.val hxy
  · intro x hx; exact ⟨x.val,mem_filter.mpr ⟨mem_univ _,x.property⟩,rfl⟩
  · intros; rfl

private def CompLabels {N colors l : ℕ} (F : Finset (ColoredEdge N colors)) (b : Fin N → Fin l) :
    Fin (Components F).card → Fin l := fun i => b (CompRep F i).val

private lemma edge_constant_sum {N colors l : ℕ} (F : Finset (ColoredEdge N colors))
    (G : Partition (Components F).card → ℝ) :
    (∑ b : Fin N → Fin l, if EdgeConstant F b then G (Kernel (CompLabels F b)) else 0) =
      (l:ℝ)^(N-(Vertices F).card) * ∑ x : Fin (Components F).card → Fin l, G (Kernel x) := by
  rw [sum_if_subtype]
  let e := componentLabelEquiv (l := l) F
  have he := e.symm.sum_comp (fun b : {b : Fin N → Fin l // EdgeConstant F b} => G (Kernel (CompLabels F b.val)))
  have heval (x : (Fin (Components F).card → Fin l) × ({v // v ∉ Vertices F} → Fin l)) :
      CompLabels F (e.symm x).val = x.1 := by
    exact congrArg Prod.fst (e.apply_symm_apply x)
  simp_rw [heval] at he
  rw [← he,Fintype.sum_prod_type]
  have hout : Fintype.card {v : Fin N // v ∉ Vertices F} = N-(Vertices F).card := by
    rw [Fintype.card_subtype]
    have hh : (univ.filter (fun v : Fin N => v ∉ Vertices F)) = univ\Vertices F := by ext v; simp
    rw [hh,card_sdiff_of_subset (subset_univ _),card_univ,Fintype.card_fin]
  simp only [sum_const,card_univ,Fintype.card_fun,Fintype.card_fin,hout,nsmul_eq_mul,Nat.cast_pow,← Finset.mul_sum]

private lemma kernel_sum {k l : ℕ} (G : Partition k → ℝ) :
    (∑ x : Fin k → Fin l, G (Kernel x)) =
      ∑ p : Partition k, (l:ℝ)^(Blocks p).card *
        ∑ r : Partition k, if Refines r p then (Mobius r p:ℝ)*G r else 0 := by
  have hgroup : (∑ x : Fin k → Fin l, G (Kernel x)) =
      ∑ r : Partition k, ((univ.filter (fun x : Fin k → Fin l => Kernel x = r)).card:ℝ)*G r := by
    simp only [Finset.card_eq_sum_ones,Nat.cast_sum,Nat.cast_one,Finset.sum_mul]
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
    apply sum_congr rfl
    intro x hx
    simp
  rw [hgroup]
  simp_rw [← kernel_partition_count,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro p hp
  rw [Finset.mul_sum]
  apply sum_congr rfl
  intro r hr
  split_ifs <;> ring

private lemma formal_average_identity {N colors l : ℕ} (F : Finset (ColoredEdge N colors))
    (hl : 0 < l) (G : Partition (Components F).card → ℝ) :
    Average univ (fun b : Fin N → Fin l => if EdgeConstant F b then G (Kernel (CompLabels F b)) else 0) =
      ∑ p : Partition (Components F).card,
        (l:ℝ)^(-((Vertices F).card:ℤ)+(Blocks p).card) *
          ∑ r : Partition (Components F).card, if Refines r p then (Mobius r p:ℝ)*G r else 0 := by
  have hlr : (l:ℝ) ≠ 0 := by exact_mod_cast hl.ne'
  have hv : (Vertices F).card ≤ N := (card_le_univ _).trans_eq (Fintype.card_fin N)
  unfold Average
  rw [edge_constant_sum,kernel_sum]
  simp only [card_univ,Fintype.card_fun,Fintype.card_fin,Nat.cast_pow,Finset.mul_sum,Finset.sum_div]
  apply sum_congr rfl
  intro p hp
  have hpow : (l:ℝ)^(N-(Vertices F).card)*(l:ℝ)^(Blocks p).card/(l:ℝ)^N =
      (l:ℝ)^(-((Vertices F).card:ℤ)+(Blocks p).card) := by
    rw [← zpow_natCast,← zpow_natCast,← zpow_natCast,← zpow_add₀ hlr,← zpow_sub₀ hlr]
    congr 1
    omega
  apply sum_congr rfl
  intro r hr
  rw [← mul_assoc,← div_mul_eq_mul_div,hpow]

private def PlaceBlock {N l s : ℕ} (t : Fin N → Fin (l*s)) (v : Fin N) : Fin l :=
  (finProdFinEquiv.symm (t v)).1
private def PlaceLocal {N l s : ℕ} (t : Fin N → Fin (l*s)) (v : Fin N) : Fin s :=
  (finProdFinEquiv.symm (t v)).2
private def LocalPair {N colors l s : ℕ} (t : Fin N → Fin (l*s)) (e : ColoredEdge N colors) : Sym2 (Fin s) :=
  s(PlaceLocal t e.1,PlaceLocal t e.2.1)

private lemma place_injective {N l s : ℕ} (t : Fin N → Fin (l*s)) (ht : Function.Injective t)
    {u v : Fin N} (hb : PlaceBlock t u = PlaceBlock t v) (hx : PlaceLocal t u = PlaceLocal t v) : u = v := by
  apply ht
  apply finProdFinEquiv.symm.injective
  exact Prod.ext hb hx

private lemma incident_block {N colors l s : ℕ} (F : Finset (ColoredEdge N colors))
    (t : Fin N → Fin (l*s)) (hb : EdgeConstant F (PlaceBlock t))
    {e : ColoredEdge N colors} (he : e ∈ F) {u : Fin N} (hu : Incident e u) :
    PlaceBlock t u = PlaceBlock t e.1 := by
  rcases hu with h | h
  · exact congrArg (PlaceBlock t) h.symm
  · exact (congrArg (PlaceBlock t) h.symm).trans (hb e he).symm

private lemma local_pair_member {N colors l s : ℕ} (t : Fin N → Fin (l*s))
    (e : ColoredEdge N colors) (x : Fin s) :
    x ∈ LocalPair t e ↔ ∃ u, Incident e u ∧ PlaceLocal t u = x := by
  simp only [LocalPair,Sym2.mem_iff,Incident]
  constructor
  · rintro (h | h)
    · exact ⟨e.1,Or.inl rfl,h.symm⟩
    · exact ⟨e.2.1,Or.inr rfl,h.symm⟩
  · rintro ⟨u,(rfl | rfl),hx⟩
    · exact Or.inl hx.symm
    · exact Or.inr hx.symm

private lemma local_overlap_edges_eq {N colors l s : ℕ} (F : Finset (ColoredEdge N colors))
    (hF : Consistent F) (t : Fin N → Fin (l*s)) (ht : Function.Injective t)
    (hb : EdgeConstant F (PlaceBlock t)) {e f : ColoredEdge N colors}
    (he : e ∈ F) (hf : f ∈ F) (hc : e.2.2 = f.2.2) (hj : PlaceBlock t e.1 = PlaceBlock t f.1)
    {x : Fin s} (hx : x ∈ LocalPair t e) (hy : x ∈ LocalPair t f) : e = f := by
  obtain ⟨u,hu,hux⟩ := (local_pair_member t e x).mp hx
  obtain ⟨v,hv,hvx⟩ := (local_pair_member t f x).mp hy
  have huv : u = v := place_injective t ht
    ((incident_block F t hb he hu).trans (hj.trans (incident_block F t hb hf hv).symm))
    (hux.trans hvx.symm)
  exact hF.2 e he f hf hc ⟨u,hu,huv ▸ hv⟩

private def ProjectedEdges {N colors l s : ℕ} (F : Finset (ColoredEdge N colors))
    (t : Fin N → Fin (l*s)) (c : Fin colors) (j : Fin l) : Finset (Sym2 (Fin s)) :=
  (F.filter (fun e => e.2.2 = c ∧ PlaceBlock t e.1 = j)).image (LocalPair t)

private lemma projected_edges_loopless {N colors l s : ℕ} (F : Finset (ColoredEdge N colors))
    (hF : Consistent F) (t : Fin N → Fin (l*s)) (ht : Function.Injective t)
    (hb : EdgeConstant F (PlaceBlock t)) (c : Fin colors) (j : Fin l) :
    ∀ p ∈ ProjectedEdges F t c j, ¬ p.IsDiag := by
  intro p hp
  obtain ⟨e,he,rfl⟩ := mem_image.mp hp
  have heF := (mem_filter.mp he).1
  rw [LocalPair,Sym2.mk_isDiag_iff]
  intro heq
  have hv := place_injective t ht (hb e heF) heq
  exact (ne_of_lt (hF.1 e heF)) hv

private lemma projected_edges_disjoint {N colors l s : ℕ} (F : Finset (ColoredEdge N colors))
    (hF : Consistent F) (t : Fin N → Fin (l*s)) (ht : Function.Injective t)
    (hb : EdgeConstant F (PlaceBlock t)) (c : Fin colors) (j : Fin l) :
    ∀ p ∈ ProjectedEdges F t c j, ∀ q ∈ ProjectedEdges F t c j,
      (∃ x, x ∈ p ∧ x ∈ q) → p = q := by
  intro p hp q hq hxy
  obtain ⟨e,he,rfl⟩ := mem_image.mp hp
  obtain ⟨f,hf,rfl⟩ := mem_image.mp hq
  obtain ⟨x,hx,hy⟩ := hxy
  have heF := (mem_filter.mp he).1
  have hfF := (mem_filter.mp hf).1
  have hc := (mem_filter.mp he).2.1.trans (mem_filter.mp hf).2.1.symm
  have hj := (mem_filter.mp he).2.2.trans (mem_filter.mp hf).2.2.symm
  rw [local_overlap_edges_eq F hF t ht hb heF hfF hc hj hx hy]

private lemma projected_edges_card {N colors l s : ℕ} (F : Finset (ColoredEdge N colors))
    (hF : Consistent F) (t : Fin N → Fin (l*s)) (ht : Function.Injective t)
    (hb : EdgeConstant F (PlaceBlock t)) (c : Fin colors) (j : Fin l) :
    (ProjectedEdges F t c j).card = (F.filter (fun e => e.2.2 = c ∧ PlaceBlock t e.1 = j)).card := by
  apply card_image_of_injOn
  intro e he f hf heq
  have hx : PlaceLocal t e.1 ∈ LocalPair t e := Sym2.mem_mk_left _ _
  have hy : PlaceLocal t e.1 ∈ LocalPair t f := heq ▸ hx
  exact local_overlap_edges_eq F hF t ht hb (mem_filter.mp he).1 (mem_filter.mp hf).1
    ((mem_filter.mp he).2.1.trans (mem_filter.mp hf).2.1.symm)
    ((mem_filter.mp he).2.2.trans (mem_filter.mp hf).2.2.symm) hx hy

private lemma place_coordinates {N l s : ℕ} (t : Fin N → Fin (l*s)) (v : Fin N) :
    t v = finProdFinEquiv (PlaceBlock t v,PlaceLocal t v) :=
  (finProdFinEquiv.apply_symm_apply (t v)).symm

private lemma projected_event {N colors l s : ℕ} (F : Finset (ColoredEdge N colors))
    (t : Fin N → Fin (l*s)) (hb : EdgeConstant F (PlaceBlock t)) (c : Fin colors)
    (h : Fin (l*s) → Fin (l*s)) (hh : h ∈ Matchings (l*s) l) :
    (∀ e ∈ F, e.2.2 = c → h (t e.1) = t e.2.1) ↔
      (∀ j a b, s(a,b) ∈ ProjectedEdges F t c j →
        h (finProdFinEquiv (j,a)) = finProdFinEquiv (j,b)) := by
  constructor
  · intro hc j a b hp
    obtain ⟨e,he,heq⟩ := mem_image.mp hp
    have heF := (mem_filter.mp he).1
    have hej := (mem_filter.mp he).2.2
    have hec := (mem_filter.mp he).2.1
    have hu : t e.1 = finProdFinEquiv (j,PlaceLocal t e.1) := by rw [place_coordinates t e.1,hej]
    have hv : t e.2.1 = finProdFinEquiv (j,PlaceLocal t e.2.1) := by rw [place_coordinates t e.2.1,← hb e heF,hej]
    change s(PlaceLocal t e.1,PlaceLocal t e.2.1) = s(a,b) at heq
    rcases Sym2.eq_iff.mp heq with ⟨ha,hb⟩ | ⟨ha,hb⟩
    · simpa only [hu,hv,ha,hb] using hc e heF hec
    · have hinv := ((mem_filter.mp hh).2.1 (t e.1)).1
      rw [hc e heF hec] at hinv
      simpa only [hu,hv,ha,hb] using hinv
  · intro hc e he hec
    let j := PlaceBlock t e.1
    have hp : LocalPair t e ∈ ProjectedEdges F t c j :=
      mem_image.mpr ⟨e,mem_filter.mpr ⟨he,hec,rfl⟩,rfl⟩
    have heq := hc j (PlaceLocal t e.1) (PlaceLocal t e.2.1) hp
    have hu : t e.1 = finProdFinEquiv (j,PlaceLocal t e.1) := place_coordinates t e.1
    have hv : t e.2.1 = finProdFinEquiv (j,PlaceLocal t e.2.1) := by rw [place_coordinates t e.2.1,← hb e he]
    simpa only [← hu,← hv] using heq

private lemma matchingMoment_block (l s n : ℕ) (hl : 0 < l) :
    MatchingMoment n (l*s) l = ∏ a ∈ range n, ((s:ℝ)-2*a-1)⁻¹ := by
  unfold MatchingMoment
  apply prod_congr rfl
  intro a ha
  have hlr : (l:ℝ) ≠ 0 := by exact_mod_cast hl.ne'
  have hc : ((2*(a+1)-1:ℕ):ℝ) = 2*(a:ℝ)+1 := by
    rw [show 2*(a+1)-1=2*a+1 by omega]
    push_cast
    rfl
  rw [hc]
  have heq : (l:ℝ)*s-(2*(a:ℝ)+1)*l = (l:ℝ)*((s:ℝ)-2*a-1) := by ring
  rw [heq,div_mul_eq_div_div,div_self hlr,one_div]

private lemma average_congr {α : Type*} (s : Finset α) (f g : α → ℝ)
    (h : ∀ x ∈ s, f x = g x) : Average s f = Average s g := by
  unfold Average
  congr 1
  exact sum_congr rfl h

private lemma color_pattern_probability {N colors l s : ℕ} (F : Finset (ColoredEdge N colors))
    (hF : Consistent F) (t : Fin N → Fin (l*s)) (ht : Function.Injective t)
    (hb : EdgeConstant F (PlaceBlock t)) (c : Fin colors) (hl : 0 < l) (hs : Even s) :
    Average (Matchings (l*s) l) (fun h => if ∀ e ∈ F, e.2.2 = c → h (t e.1) = t e.2.1 then (1:ℝ) else 0) =
      ∏ j : Fin l, MatchingMoment (F.filter (fun e => e.2.2 = c ∧ PlaceBlock t e.1 = j)).card (l*s) l := by
  have he := uniform_block_matching_contains l s hl hs (ProjectedEdges F t c)
    (projected_edges_loopless F hF t ht hb c) (projected_edges_disjoint F hF t ht hb c)
  have hc : Average (Matchings (l*s) l)
      (fun h => if ∀ e ∈ F, e.2.2 = c → h (t e.1) = t e.2.1 then (1:ℝ) else 0) =
      Average (Matchings (l*s) l) (fun h => if ∀ j a b, s(a,b) ∈ ProjectedEdges F t c j →
        h (finProdFinEquiv (j,a)) = finProdFinEquiv (j,b) then (1:ℝ) else 0) := by
    apply average_congr
    intro h hh
    have hi := projected_event F t hb c h hh
    by_cases hevent : ∀ e ∈ F, e.2.2 = c → h (t e.1) = t e.2.1
    · rw [if_pos hevent,if_pos (hi.mp hevent)]
    · rw [if_neg hevent,if_neg (fun hp => hevent (hi.mpr hp))]
  rw [hc,he]
  apply prod_congr rfl
  intro j hj
  rw [projected_edges_card F hF t ht hb c j,matchingMoment_block l s _ hl]

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

private lemma average_subtype {α : Type*} (s : Finset α) (f : α → ℝ) :
    Average s f = Average univ (fun x : s => f x.val) := by
  simp only [Average,card_univ,Fintype.card_coe,Finset.sum_coe_sort]

private lemma average_pi_subset {I α : Type*} [Fintype I] [Fintype α] [DecidableEq I]
    (S : Finset α) (f : (I → α) → ℝ) :
    Average (univ.filter (fun h : I → α => ∀ i, h i ∈ S)) f =
      Average univ (fun h : I → S => f (fun i => (h i).val)) := by
  rw [average_subtype]
  let e : {h : I → α // h ∈ univ.filter (fun h => ∀ i, h i ∈ S)} ≃ (I → S) :=
    (Equiv.subtypeEquiv (Equiv.refl (I → α)) (by intro h; simp)).trans Equiv.subtypePiEquivPi
  have he := e.symm.sum_comp (fun h => f h.val)
  unfold Average
  simp only [card_univ]
  rw [Fintype.card_congr e]
  congr 1
  exact he.symm

private lemma average_pi_product {I α : Type*} [Fintype I] [Fintype α] [DecidableEq I]
    (S : Finset α) (f : I → α → ℝ) :
    Average (univ.filter (fun h : I → α => ∀ i, h i ∈ S)) (fun h => ∏ i, f i (h i)) =
      ∏ i, Average S (f i) := by
  rw [average_pi_subset]
  have hh := average_product (fun i (x : S) => f i x.val)
  rw [hh]
  apply prod_congr rfl
  intro i hi
  exact (average_subtype S (f i)).symm

private lemma matching_pattern_probability {N colors l s : ℕ} (F : Finset (ColoredEdge N colors))
    (hF : Consistent F) (t : Fin N → Fin (l*s)) (ht : Function.Injective t)
    (hb : EdgeConstant F (PlaceBlock t)) (hl : 0 < l) (hs : Even s) :
    MatchingAverage l t (fun G : Finset (ColoredEdge N colors) => if F ⊆ G then (1:ℝ) else 0) =
      ∏ c : Fin colors, ∏ j : Fin l,
        MatchingMoment (F.filter (fun e => e.2.2 = c ∧ PlaceBlock t e.1 = j)).card (l*s) l := by
  have hevent (h : Fin colors → (Fin (l*s) → Fin (l*s))) :
      (F ⊆ VisibleEdges t h) ↔ ∀ c, ∀ e ∈ F, e.2.2 = c → h c (t e.1) = t e.2.1 := by
    constructor
    · intro hh c e he hec
      have hr := (mem_filter.mp (hh he)).2.2
      simpa only [hec] using hr
    · intro hh e he
      exact mem_filter.mpr ⟨mem_univ _,hF.1 e he,hh e.2.2 e he rfl⟩
  have hind (h : Fin colors → (Fin (l*s) → Fin (l*s))) :
      (if F ⊆ VisibleEdges t h then (1:ℝ) else 0) =
      ∏ c : Fin colors, if ∀ e ∈ F, e.2.2 = c → h c (t e.1) = t e.2.1 then (1:ℝ) else 0 := by
    by_cases hh : ∀ c, ∀ e ∈ F, e.2.2 = c → h c (t e.1) = t e.2.1
    · rw [if_pos ((hevent h).mpr hh)]
      symm
      exact prod_eq_one (fun c hc => if_pos (hh c))
    · rw [if_neg (fun hc => hh ((hevent h).mp hc))]
      symm
      obtain ⟨c,hc⟩ := not_forall.mp hh
      exact Finset.prod_eq_zero (mem_univ c) (if_neg hc)
  unfold MatchingAverage
  simp_rw [hind]
  calc
    _ = ∏ c : Fin colors, Average (Matchings (l*s) l)
        (fun h => if ∀ e ∈ F, e.2.2 = c → h (t e.1) = t e.2.1 then (1:ℝ) else 0) := by
      convert average_pi_product (Matchings (l*s) l)
        (fun c h => if ∀ e ∈ F, e.2.2 = c → h (t e.1) = t e.2.1 then (1:ℝ) else 0) using 2
      ext h
      simp only [mem_filter,mem_univ,true_and]
    _ = _ := by
      apply prod_congr rfl
      intro c hc
      exact color_pattern_probability F hF t ht hb c hl hs

private lemma matching_pattern_zero {N colors l s : ℕ} (F : Finset (ColoredEdge N colors))
    (t : Fin N → Fin (l*s)) (hb : ¬ EdgeConstant F (PlaceBlock t)) (hl : 0 < l) :
    MatchingAverage l t (fun G : Finset (ColoredEdge N colors) => if F ⊆ G then (1:ℝ) else 0) = 0 := by
  unfold EdgeConstant at hb
  push_neg at hb
  obtain ⟨e,he,hbe⟩ := hb
  unfold MatchingAverage Average
  have hsum : (∑ h ∈ univ.filter (fun h : Fin colors → (Fin (l*s) → Fin (l*s)) =>
      ∀ c, h c ∈ Matchings (l*s) l), if F ⊆ VisibleEdges t h then (1:ℝ) else 0) = 0 := by
    apply sum_eq_zero
    intro h hh
    apply if_neg
    intro hsub
    have heq := (mem_filter.mp (hsub he)).2.2
    have hm := (mem_filter.mp ((mem_filter.mp hh).2 e.2.2)).2.2 (t e.1)
    rw [Nat.mul_div_cancel_left s hl,heq] at hm
    apply hbe
    apply Fin.ext
    exact hm.symm
  rw [hsum,zero_div]

private lemma component_edge_weights {N colors : ℕ} (F : Finset (ColoredEdge N colors))
    (f : ColoredEdge N colors → ℕ) :
    (∑ i : Fin (Components F).card, ∑ e ∈ F, if e.1 ∈ ComponentAt F i then f e else 0) =
      ∑ e ∈ F, f e := by
  rw [sum_componentAt F (fun S => ∑ e ∈ F, if e.1 ∈ S then f e else 0),Finset.sum_comm]
  apply sum_congr rfl
  intro e he
  have hu := (endpoints_mem F e he).1
  have hc : fullClass F e.1 ∈ Components F :=
    mem_image.mpr ⟨e.1,hu,component_fullClass F hu⟩
  have hh : (∑ S ∈ Components F, if e.1 ∈ S then f e else 0) =
      ∑ S ∈ Components F, if S = fullClass F e.1 then f e else 0 := by
    apply sum_congr rfl
    intro S hS
    simp only [component_containing F e.1 hu S hS]
  rw [hh]
  simp [hc]

private lemma label_edge_counts {N colors l : ℕ} (F : Finset (ColoredEdge N colors))
    (b : Fin N → Fin l) (hb : EdgeConstant F b) (c : Fin colors) (j : Fin l) :
    (∑ i ∈ univ.filter (fun i => CompLabels F b i = j), ComponentColorCount F i c) =
      (F.filter (fun e => e.2.2 = c ∧ b e.1 = j)).card := by
  rw [Finset.sum_filter]
  unfold ComponentColorCount
  simp_rw [Finset.card_eq_sum_ones,Finset.sum_filter]
  have hsplit (i : Fin (Components F).card) :
      (if CompLabels F b i = j then ∑ e ∈ F, if e.1 ∈ ComponentAt F i ∧ e.2.2 = c then (1:ℕ) else 0 else 0) =
      ∑ e ∈ F, if CompLabels F b i = j then (if e.1 ∈ ComponentAt F i ∧ e.2.2 = c then (1:ℕ) else 0) else 0 := by
    by_cases h : CompLabels F b i = j <;> simp [h]
  simp_rw [hsplit]
  have hpoint (i : Fin (Components F).card) (e : ColoredEdge N colors) (he : e ∈ F) :
      (if CompLabels F b i = j then (if e.1 ∈ ComponentAt F i ∧ e.2.2 = c then (1:ℕ) else 0) else 0) =
      (if e.1 ∈ ComponentAt F i then (if e.2.2 = c ∧ b e.1 = j then (1:ℕ) else 0) else 0) := by
    by_cases hmem : e.1 ∈ ComponentAt F i
    · have hx : b e.1 = CompLabels F b i := component_constant F b hb i hmem (rep_mem F i)
      simp only [hmem,true_and,hx]
      by_cases hc : e.2.2 = c <;> by_cases hj : CompLabels F b i = j <;> simp [hc,hj]
    · simp [hmem]
  have heq : (∑ i : Fin (Components F).card, ∑ e ∈ F,
      if CompLabels F b i = j then (if e.1 ∈ ComponentAt F i ∧ e.2.2 = c then (1:ℕ) else 0) else 0) =
      ∑ i : Fin (Components F).card, ∑ e ∈ F,
        if e.1 ∈ ComponentAt F i then (if e.2.2 = c ∧ b e.1 = j then (1:ℕ) else 0) else 0 := by
    apply sum_congr rfl
    intro i hi
    exact sum_congr rfl (fun e he => hpoint i e he)
  rw [heq,component_edge_weights]

private lemma matching_pattern_component {N colors l s : ℕ} (F : Finset (ColoredEdge N colors))
    (hF : Consistent F) (t : Fin N → Fin (l*s)) (ht : Function.Injective t)
    (hl : 0 < l) (hs : Even s) :
    MatchingAverage l t (fun G : Finset (ColoredEdge N colors) => if F ⊆ G then (1:ℝ) else 0) =
      if EdgeConstant F (PlaceBlock t) then
        CountMoment (ComponentColorCount F) (Kernel (CompLabels F (PlaceBlock t))) (l*s) l else 0 := by
  by_cases hb : EdgeConstant F (PlaceBlock t)
  · rw [if_pos hb,matching_pattern_probability F hF t ht hb hl hs,kernel_moment,Finset.prod_comm]
    apply prod_congr rfl
    intro j hj
    apply prod_congr rfl
    intro c hc
    rw [label_edge_counts F (PlaceBlock t) hb c j]
  · rw [if_neg hb,matching_pattern_zero F t hb hl]

private def BlockFunctional {N colors l : ℕ} (F : Finset (ColoredEdge N colors))
    (b : Fin N → Fin l) (M a : ℝ) : ℝ :=
  if EdgeConstant F b then CountMoment (ComponentColorCount F) (Kernel (CompLabels F b)) M a else 0

private lemma average_const_nonempty {α : Type*} (S : Finset α) (hS : S.Nonempty) (c : ℝ) :
    Average S (fun _ => c) = c := by
  have hc : (S.card:ℝ) ≠ 0 := by exact_mod_cast hS.card_pos.ne'
  simp [Average,hc]

private lemma feasible_pattern_conditional {N colors l s : ℕ} (F : Finset (ColoredEdge N colors))
    (hF : Consistent F) (hl : 0 < l) (hs : Even s) :
    FeasibleBase N (l*s) l (fun G : Finset (ColoredEdge N colors) => if F ⊆ G then (1:ℝ) else 0) =
      Average (univ.filter (NoOverflow N (l*s) l)) (fun b => BlockFunctional F b (l*s) l) := by
  unfold FeasibleBase
  apply average_congr
  intro b hb
  have hcap : ∀ j, (univ.filter (fun v => b v = j)).card ≤ s := by
    simpa only [NoOverflow,Nat.mul_div_cancel_left s hl] using (mem_filter.mp hb).2
  have hEmb := embeddings_nonempty hl b hcap
  have heq : Average (Embeddings (l*s) b)
      (fun t => MatchingAverage l t (fun G : Finset (ColoredEdge N colors) => if F ⊆ G then (1:ℝ) else 0)) =
      Average (Embeddings (l*s) b) (fun _ => BlockFunctional F b (l*s) l) := by
    apply average_congr
    intro t ht
    have htinj := (mem_filter.mp ht).2.1
    have htblock := (mem_filter.mp ht).2.2
    have htb : PlaceBlock t = b := by
      funext v
      apply Fin.ext
      change (t v).val/s = (b v).val
      simpa only [Nat.mul_div_cancel_left s hl] using htblock v
    have hh := matching_pattern_component F hF t htinj hl hs
    simpa only [BlockFunctional,htb] using hh
  rw [heq,average_const_nonempty _ hEmb]

private lemma block_functional_average {N colors l : ℕ} (F : Finset (ColoredEdge N colors))
    (hl : 0 < l) (M : ℝ) :
    Average univ (fun b : Fin N → Fin l => BlockFunctional F b M l) = TopologyMoment F M l := by
  simpa only [BlockFunctional,TopologyMoment,PartitionCorrection,PartitionMoment,CountMoment] using
    (formal_average_identity F hl (fun p => CountMoment (ComponentColorCount F) p M l))

private lemma matchingMoment_bounds (l s n : ℕ) (hl : 0 < l) (hn : 2*n ≤ s) :
    0 ≤ MatchingMoment n (l*s) l ∧ MatchingMoment n (l*s) l ≤ 1 := by
  rw [matchingMoment_block l s n hl]
  have hterm (a : ℕ) (ha : a ∈ range n) :
      0 ≤ ((s:ℝ)-2*a-1)⁻¹ ∧ ((s:ℝ)-2*a-1)⁻¹ ≤ 1 := by
    have ha' := mem_range.mp ha
    have hn' : 2*a+2 ≤ s := by omega
    have hr : (1:ℝ) ≤ (s:ℝ)-2*a-1 := by
      have hh : (2:ℝ)*a+2 ≤ s := by exact_mod_cast hn'
      linarith
    exact ⟨inv_nonneg.mpr (by linarith),inv_le_one_of_one_le₀ hr⟩
  exact ⟨prod_nonneg (fun a ha => (hterm a ha).1),prod_le_one (fun a ha => (hterm a ha).1) (fun a ha => (hterm a ha).2)⟩

private lemma block_functional_bounds {N colors l s : ℕ} (F : Finset (ColoredEdge N colors))
    (hl : 0 < l) (hsmall : 2*F.card ≤ s) (b : Fin N → Fin l) :
    0 ≤ BlockFunctional F b (l*s) l ∧ BlockFunctional F b (l*s) l ≤ 1 := by
  unfold BlockFunctional
  split_ifs with hb
  · rw [kernel_moment]
    have hterm (j : Fin l) (c : Fin colors) :
        0 ≤ MatchingMoment (∑ i ∈ univ.filter (fun i => CompLabels F b i = j), ComponentColorCount F i c) (l*s) l ∧
        MatchingMoment (∑ i ∈ univ.filter (fun i => CompLabels F b i = j), ComponentColorCount F i c) (l*s) l ≤ 1 := by
      rw [label_edge_counts F b hb c j]
      apply matchingMoment_bounds l s _ hl
      have hh := card_filter_le F (fun e => e.2.2 = c ∧ b e.1 = j)
      omega
    have hinner (j : Fin l) :
        0 ≤ ∏ c : Fin colors, MatchingMoment (∑ i ∈ univ.filter (fun i => CompLabels F b i = j), ComponentColorCount F i c) (l*s) l ∧
        (∏ c : Fin colors, MatchingMoment (∑ i ∈ univ.filter (fun i => CompLabels F b i = j), ComponentColorCount F i c) (l*s) l) ≤ 1 := by
      exact ⟨prod_nonneg (fun c hc => (hterm j c).1),prod_le_one (fun c hc => (hterm j c).1) (fun c hc => (hterm j c).2)⟩
    exact ⟨prod_nonneg (fun j hj => (hinner j).1),prod_le_one (fun j hj => (hinner j).1) (fun j hj => (hinner j).2)⟩
  · exact ⟨le_rfl,by norm_num⟩

private lemma finite_topology_comparison {N colors l s : ℕ} (F : Finset (ColoredEdge N colors))
    (hF : Consistent F) (hl : 0 < l) (hs : Even s) (hsmall : 2*F.card ≤ s) :
    |FeasibleBase N (l*s) l (fun G : Finset (ColoredEdge N colors) => if F ⊆ G then (1:ℝ) else 0)-
      TopologyMoment F (l*s) l| ≤ OverflowProbability N (l*s) l := by
  rw [feasible_pattern_conditional F hF hl hs,← block_functional_average F hl]
  have hh := conditioning_error (univ : Finset (Fin N → Fin l)) (univ.filter (NoOverflow N (l*s) l))
    (fun b => BlockFunctional F b (l*s) l) (filter_subset _ _)
    (fun b hb => block_functional_bounds F hl hsmall b)
  simpa only [OverflowProbability,mem_filter,mem_univ,true_and] using hh

end
end QuantumBipartiteTesting.Bipartiteness.SamplingProof

open QuantumBipartiteTesting.Bipartiteness
open QuantumBipartiteTesting.Bipartiteness.SamplingProof
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

theorem solution {N colors : ℕ} (M l : ℕ) (hv : ValidParameters N M l)
    (F : Finset (ColoredEdge N colors)) (hF : Consistent F) (hsmall : 2*F.card ≤ M/l) :
    |FeasibleBase N M l (fun G : Finset (ColoredEdge N colors) => if F ⊆ G then (1:ℝ) else 0)-
      TopologyMoment F M l| ≤ OverflowProbability N M l := by
  have hl : 0 < l := hv.1
  obtain ⟨a,ha⟩ := hv.2.2
  have hM : M = l*(2*a) := by rw [ha]; ring
  rw [hM] at hsmall ⊢
  have hs : Even (2*a) := ⟨a,by omega⟩
  have hcap : 2*F.card ≤ 2*a := by simpa only [Nat.mul_div_cancel_left (2*a) hl] using hsmall
  have hh := finite_topology_comparison F hF hl hs hcap
  simpa only [Nat.cast_mul,Nat.cast_ofNat] using hh
end
