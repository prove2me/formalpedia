-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P38.lemma6
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T10:53:55.578988+00:00
-- url     : https://prove2.me/submissions/9f29f631-3f2e-43b1-ae84-3dcce64f5932

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P38

-- ===== P38L6 =====

noncomputable section

namespace X4P38L6

open QAlgorithms.Papers.Independent.Support50.P38 Finset

variable {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
  [DecidableEq A] [DecidableEq B] [DecidableEq C] {n : ℕ}

lemma occ_eq (z : Fin n → C) (a : C) : occurrences z a = Fintype.card {i // z i = a} :=
  (Fintype.card_subtype _).symm

lemma occ_perm (z : Fin n → C) (π : Equiv.Perm (Fin n)) (a : C) :
    occurrences (z ∘ π) a = occurrences z a := by
  rw [occ_eq, occ_eq]
  exact Fintype.card_congr (π.subtypeEquiv (fun i => Iff.rfl))

lemma mem_tw {t : ExactType C n} {z : Fin n → C} :
    z ∈ typeWords t ↔ ∀ a, occurrences z a = t.count a := by
  unfold typeWords; simp

lemma perm_of (x x' : Fin n → C) (h : ∀ a, occurrences x a = occurrences x' a) :
    ∃ π : Equiv.Perm (Fin n), x' = x ∘ π := by
  have e : ∀ c, {i // x' i = c} ≃ {i // x i = c} := fun c =>
    Fintype.equivOfCardEq (by rw [← occ_eq, ← occ_eq, h])
  refine ⟨Equiv.ofFiberEquiv e, funext fun i => ?_⟩
  exact (Equiv.ofFiberEquiv_map e i).symm

lemma tw_perm {t : ExactType C n} {z : Fin n → C} (hz : z ∈ typeWords t)
    (π : Equiv.Perm (Fin n)) : z ∘ π ∈ typeWords t := by
  rw [mem_tw] at *; intro a; rw [occ_perm, hz]

/-- zipped word -/
def zp (x : Fin n → A) (y : Fin n → B) : Fin n → A × B := fun i => (x i, y i)

lemma occ_left (x : Fin n → A) (y : Fin n → B) (a : A) :
    occurrences x a = ∑ b, occurrences (zp x y) (a, b) := by
  unfold occurrences
  rw [card_eq_sum_card_fiberwise (f := y) (t := univ) (fun _ _ => mem_coe.2 (mem_univ _))]
  refine sum_congr rfl fun b _ => ?_
  rw [filter_filter]; congr 1; ext i; simp [zp, Prod.ext_iff]

lemma occ_right (x : Fin n → A) (y : Fin n → B) (b : B) :
    occurrences y b = ∑ a, occurrences (zp x y) (a, b) := by
  unfold occurrences
  rw [card_eq_sum_card_fiberwise (f := x) (t := univ) (fun _ _ => mem_coe.2 (mem_univ _))]
  refine sum_congr rfl fun a _ => ?_
  rw [filter_filter]; congr 1; ext i; simp [zp, Prod.ext_iff, and_comm]

lemma compat_iff (t : ExactType (A × B) n) (x : Fin n → A) (y : Fin n → B) :
    JointTypeWordsCompatible t x y ↔ zp x y ∈ typeWords t := Iff.rfl

lemma compat_left {t : ExactType (A × B) n} {x : Fin n → A} {y : Fin n → B}
    (h : JointTypeWordsCompatible t x y) : x ∈ typeWords t.left := by
  rw [compat_iff, mem_tw] at h
  rw [mem_tw]; intro a; rw [occ_left x y a]; simp only [h]; rfl

lemma compat_right {t : ExactType (A × B) n} {x : Fin n → A} {y : Fin n → B}
    (h : JointTypeWordsCompatible t x y) : y ∈ typeWords t.right := by
  rw [compat_iff, mem_tw] at h
  rw [mem_tw]; intro b; rw [occ_right x y b]; simp only [h]; rfl

lemma zp_perm (x : Fin n → A) (y : Fin n → B) (π : Equiv.Perm (Fin n)) :
    zp (x ∘ π) (y ∘ π) = zp x y ∘ π := rfl

lemma fib_card_eq (t : ExactType (A × B) n) (x x' : Fin n → A) (π : Equiv.Perm (Fin n))
    (hx : x' = x ∘ π) : (forwardFiber t x').card = (forwardFiber t x).card := by
  subst hx
  symm
  refine card_nbij' (fun y => y ∘ π) (fun y => y ∘ π.symm) ?_ ?_ ?_ ?_
  · intro y hy
    simp only [forwardFiber, coe_filter, Set.mem_setOf_eq, mem_univ, true_and] at hy ⊢
    rw [compat_iff, zp_perm]; exact tw_perm hy π
  · intro y hy
    simp only [forwardFiber, coe_filter, Set.mem_setOf_eq, mem_univ, true_and] at hy ⊢
    rw [compat_iff] at hy ⊢
    have := tw_perm hy π.symm
    rw [← zp_perm] at this
    convert this using 2; funext i; simp
  · intro y _; funext i; simp
  · intro y _; funext i; simp

lemma rfib_card_eq (t : ExactType (A × B) n) (y y' : Fin n → B) (π : Equiv.Perm (Fin n))
    (hy : y' = y ∘ π) : (reverseFiber t y').card = (reverseFiber t y).card := by
  subst hy
  symm
  refine card_nbij' (fun x => x ∘ π) (fun x => x ∘ π.symm) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [reverseFiber, coe_filter, Set.mem_setOf_eq, mem_univ, true_and] at hx ⊢
    rw [compat_iff, zp_perm]; exact tw_perm hx π
  · intro x hx
    simp only [reverseFiber, coe_filter, Set.mem_setOf_eq, mem_univ, true_and] at hx ⊢
    rw [compat_iff] at hx ⊢
    have := tw_perm hx π.symm
    rw [← zp_perm] at this
    convert this using 2; funext i; simp
  · intro x _; funext i; simp
  · intro x _; funext i; simp

lemma same_type {s : ExactType C n} {x x' : Fin n → C} (hx : x ∈ typeWords s)
    (hx' : x' ∈ typeWords s) : ∀ a, occurrences x a = occurrences x' a := by
  rw [mem_tw] at hx hx'; intro a; rw [hx, hx']

/-- |T_T| = |T_R| · |T_T(x)| for x in the left type class. -/
lemma card_left (t : ExactType (A × B) n) (x : Fin n → A) (hx : x ∈ typeWords t.left) :
    (typeWords t).card = (typeWords t.left).card * (forwardFiber t x).card := by
  rw [card_eq_sum_card_fiberwise (f := fun z i => (z i).1) (t := typeWords t.left)]
  · rw [← smul_eq_mul, ← sum_const]
    refine sum_congr rfl fun x' hx' => ?_
    obtain ⟨π, hπ⟩ := perm_of x x' (same_type hx hx')
    rw [← fib_card_eq t x x' π hπ]
    refine card_nbij' (fun z i => (z i).2) (fun y => zp x' y) ?_ ?_ ?_ ?_
    · intro z hz
      simp only [coe_filter, Set.mem_setOf_eq] at hz
      simp only [forwardFiber, coe_filter, Set.mem_setOf_eq, mem_univ, true_and]
      rw [compat_iff, ← hz.2]; exact hz.1
    · intro y hy
      simp only [forwardFiber, coe_filter, Set.mem_setOf_eq, mem_univ, true_and] at hy
      simp only [coe_filter, Set.mem_setOf_eq]
      exact ⟨hy, rfl⟩
    · intro z hz
      simp only [coe_filter, Set.mem_setOf_eq] at hz
      funext i; simp [zp, ← hz.2]
    · intro y _; rfl
  · intro z hz
    have : JointTypeWordsCompatible t (fun i => (z i).1) (fun i => (z i).2) := hz
    exact compat_left this

lemma card_right (t : ExactType (A × B) n) (y : Fin n → B) (hy : y ∈ typeWords t.right) :
    (typeWords t).card = (typeWords t.right).card * (reverseFiber t y).card := by
  rw [card_eq_sum_card_fiberwise (f := fun z i => (z i).2) (t := typeWords t.right)]
  · rw [← smul_eq_mul, ← sum_const]
    refine sum_congr rfl fun y' hy' => ?_
    obtain ⟨π, hπ⟩ := perm_of y y' (same_type hy hy')
    rw [← rfib_card_eq t y y' π hπ]
    refine card_nbij' (fun z i => (z i).1) (fun x => zp x y') ?_ ?_ ?_ ?_
    · intro z hz
      simp only [coe_filter, Set.mem_setOf_eq] at hz
      simp only [reverseFiber, coe_filter, Set.mem_setOf_eq, mem_univ, true_and]
      rw [compat_iff, ← hz.2]; exact hz.1
    · intro x hx
      simp only [reverseFiber, coe_filter, Set.mem_setOf_eq, mem_univ, true_and] at hx
      simp only [coe_filter, Set.mem_setOf_eq]
      exact ⟨hx, rfl⟩
    · intro z hz
      simp only [coe_filter, Set.mem_setOf_eq] at hz
      funext i; simp [zp, ← hz.2]
    · intro x _; rfl
  · intro z hz
    have : JointTypeWordsCompatible t (fun i => (z i).1) (fun i => (z i).2) := hz
    exact compat_right this

/-- product over a word of a given type -/
lemma prod_type {M : Type} [CommMonoid M] (s : ExactType C n) (z : Fin n → C)
    (hz : z ∈ typeWords s) (f : C → M) : ∏ i, f (z i) = ∏ c, f c ^ s.count c := by
  rw [← prod_fiberwise_of_maps_to (g := z) (t := univ) (fun _ _ => mem_univ _)]
  refine prod_congr rfl fun c _ => ?_
  rw [mem_tw] at hz
  rw [prod_congr rfl (fun i hi => by rw [(mem_filter.1 hi).2]), prod_const, ← hz c]
  rfl

/-- every exact type class is nonempty -/
lemma tw_nonempty (s : ExactType C n) : (typeWords s).Nonempty := by
  classical
  set m : Multiset C := ∑ c, s.count c • {c}
  have hm : Multiset.card m = n := by simp [m, s.total]
  set l := m.toList
  have hl : l.length = n := by simp [l, hm]
  refine ⟨fun i => l.get (Fin.cast hl.symm i), ?_⟩
  rw [mem_tw]; intro a
  have h1 : occurrences (fun i => l.get (Fin.cast hl.symm i)) a =
      Multiset.count a (Multiset.map (fun i => l.get (Fin.cast hl.symm i)) univ.val) := by
    rw [Multiset.count_map]; unfold occurrences
    rw [Finset.card_def, Finset.filter_val]; congr 1
    apply Multiset.filter_congr; intro i _; exact eq_comm
  rw [h1, Fin.univ_val_map]
  have h2 : List.ofFn (fun i => l.get (Fin.cast hl.symm i)) = l := by
    apply List.ext_get (by simp [hl]); intro k h1 h2; simp
  rw [h2]
  have : (l : Multiset C) = m := Multiset.coe_toList m
  rw [this]; simp [m, Multiset.count_sum', Multiset.count_singleton]

end X4P38L6

-- ===== P38L6Sol =====

noncomputable section

open QAlgorithms.Papers.Independent.Support50.P38

open scoped BigOperators Matrix ComplexConjugate

open Filter

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

open QAlgorithms.Papers.Independent.Frontier30.P12 (IsStochastic)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon labelInformation)

namespace X4P38L6

open Finset

attribute [local instance] Classical.propDecidable

lemma const_sum {α : Type} (s : Finset α) (f : α → ℝ) (K : ℝ) (hf : ∀ z ∈ s, f z = K)
    {x : α} (hx : x ∈ s) (hpos : 0 < ∑ z ∈ s, f z) :
    1 / (s.card : ℝ) = f x / ∑ z ∈ s, f z := by
  rw [sum_congr rfl hf, sum_const, nsmul_eq_mul, hf x hx] at *
  have hc : (s.card : ℝ) ≠ 0 := by
    have : 0 < s.card := card_pos.2 ⟨x, hx⟩
    exact_mod_cast this.ne'
  have hK : K ≠ 0 := by rintro rfl; simp at hpos
  field_simp

variable {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] {n : ℕ}

lemma tu_mem {C : Type} [Fintype C] [DecidableEq C] {s : ExactType C n} {x : Fin n → C}
    (hx : x ∈ typeWords s) : typeUniform s x = 1 / ((typeWords s).card : ℝ) := by
  unfold typeUniform; rw [if_pos hx]

lemma fwd_term (t : ExactType (A × B) n) (x : Fin n → A) (y : Fin n → B) :
    typeUniform t.left x * typeForward t x y =
      if JointTypeWordsCompatible t x y then 1 / ((typeWords t).card : ℝ) else 0 := by
  by_cases h : JointTypeWordsCompatible t x y
  · rw [if_pos h, tu_mem (compat_left h)]
    unfold typeForward; rw [if_pos h, card_left t x (compat_left h)]
    push_cast; rw [one_div_mul_one_div]
  · rw [if_neg h]; unfold typeForward; rw [if_neg h, mul_zero]

lemma rev_term (t : ExactType (A × B) n) (x : Fin n → A) (y : Fin n → B) :
    typeUniform t.right y * typeReverse t y x =
      if JointTypeWordsCompatible t x y then 1 / ((typeWords t).card : ℝ) else 0 := by
  by_cases h : JointTypeWordsCompatible t x y
  · rw [if_pos h, tu_mem (compat_right h)]
    unfold typeReverse; rw [if_pos h, card_right t y (compat_right h)]
    push_cast; rw [one_div_mul_one_div]
  · rw [if_neg h]; unfold typeReverse; rw [if_neg h, mul_zero]

lemma mem_fib {t : ExactType (A × B) n} {x : Fin n → A} {y : Fin n → B} :
    y ∈ forwardFiber t x ↔ JointTypeWordsCompatible t x y := by
  unfold forwardFiber; simp

lemma mem_rfib {t : ExactType (A × B) n} {x : Fin n → A} {y : Fin n → B} :
    x ∈ reverseFiber t y ↔ JointTypeWordsCompatible t x y := by
  unfold reverseFiber; simp

lemma part1 (t : ExactType (A × B) n) (y : Fin n → B) :
    (∑ x, typeUniform t.left x * typeForward t x y) = typeUniform t.right y := by
  simp_rw [fwd_term]
  rw [← sum_filter, sum_const, nsmul_eq_mul]
  have hf : (univ.filter fun x => JointTypeWordsCompatible t x y) = reverseFiber t y := by
    ext x; rw [mem_rfib]; simp
  rw [hf]
  by_cases hy : y ∈ typeWords t.right
  · rw [tu_mem hy, card_right t y hy]
    have hT := card_pos.2 (tw_nonempty t)
    rw [card_right t y hy] at hT
    have h1 : 0 < (reverseFiber t y).card := Nat.pos_of_mul_pos_left hT
    have h2 : 0 < (typeWords t.right).card := Nat.pos_of_mul_pos_right hT
    push_cast
    field_simp
  · have : reverseFiber t y = ∅ := by
      ext x; rw [mem_rfib]; simp only [Finset.notMem_empty, iff_false]
      exact fun h => hy (compat_right h)
    rw [this]; unfold typeUniform; rw [if_neg hy]; simp

lemma part5 (t : ExactType (A × B) n) (x : Fin n → A) (y : Fin n → B)
    (h : JointTypeWordsCompatible t x y) :
    typeForward t x y = ((typeWords t.left).card : ℝ) / (typeWords t).card ∧
      typeReverse t y x = ((typeWords t.right).card : ℝ) / (typeWords t).card := by
  have hf : 0 < (forwardFiber t x).card := card_pos.2 ⟨y, mem_fib.2 h⟩
  have hr : 0 < (reverseFiber t y).card := card_pos.2 ⟨x, mem_rfib.2 h⟩
  have hl : 0 < (typeWords t.left).card := card_pos.2 ⟨x, compat_left h⟩
  have hR : 0 < (typeWords t.right).card := card_pos.2 ⟨y, compat_right h⟩
  constructor
  · unfold typeForward; rw [if_pos h, card_left t x (compat_left h)]; push_cast
    field_simp
  · unfold typeReverse; rw [if_pos h, card_right t y (compat_right h)]; push_cast
    field_simp

end X4P38L6

attribute [local instance] Classical.propDecidable

open X4P38L6 in
theorem solution {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    [Nonempty A] [Nonempty B] {n : ℕ} (hn : 0 < n)
    (p : A → ℝ) (w : A → B → ℝ) (hp : IsLaw p) (hw : IsStochastic w)
    (t : ExactType (A × B) n) :
    (∀ y, (∑ x, typeUniform t.left x * typeForward t x y) = typeUniform t.right y) ∧
    (∀ x y, typeUniform t.left x * typeForward t x y =
      typeUniform t.right y * typeReverse t y x) ∧
    (∀ x, x ∈ typeWords t.left →
      0 < ∑ z ∈ typeWords t.left, wordMass p z →
      typeUniform t.left x = wordMass p x / (∑ z ∈ typeWords t.left, wordMass p z)) ∧
    (∀ y, y ∈ typeWords t.right →
      0 < ∑ z ∈ typeWords t.right, wordMass (sourceOutputMarginal p w) z →
      typeUniform t.right y = wordMass (sourceOutputMarginal p w) y /
        (∑ z ∈ typeWords t.right, wordMass (sourceOutputMarginal p w) z)) ∧
    (∀ x y, JointTypeWordsCompatible t x y →
      typeForward t x y = ((typeWords t.left).card : ℝ) / (typeWords t).card ∧
      typeReverse t y x = ((typeWords t.right).card : ℝ) / (typeWords t).card) ∧
    (∀ x y, JointTypeWordsCompatible t x y →
      0 < ∑ z ∈ forwardFiber t x, wordChannel w x z →
      typeForward t x y = wordChannel w x y /
        (∑ z ∈ forwardFiber t x, wordChannel w x z)) ∧
    (∀ x y, JointTypeWordsCompatible t x y →
      0 < ∑ z ∈ reverseFiber t y, wordChannel (sourceBayesReverse p w) y z →
      typeReverse t y x = wordChannel (sourceBayesReverse p w) y x /
        (∑ z ∈ reverseFiber t y, wordChannel (sourceBayesReverse p w) y z)) := by
  refine ⟨fun y => ?_, fun x y => ?_, fun x hx hpos => ?_, fun y hy hpos => ?_,
    fun x y h => ?_, fun x y h hpos => ?_, fun x y h hpos => ?_⟩
  · convert part1 t y
  · convert (fwd_term t x y).trans (rev_term t x y).symm
  · rw [tu_mem hx]
    exact const_sum _ _ (∏ a, p a ^ t.left.count a)
      (fun z hz => prod_type t.left z hz p) hx hpos
  · rw [tu_mem hy]
    exact const_sum _ _ (∏ b, sourceOutputMarginal p w b ^ t.right.count b)
      (fun z hz => prod_type t.right z hz _) hy hpos
  · convert part5 t x y h
  · have hy : y ∈ forwardFiber t x := mem_fib.2 h
    unfold typeForward; rw [if_pos h]
    refine const_sum _ _ (∏ c, w c.1 c.2 ^ t.count c) (fun z hz => ?_) hy hpos
    exact prod_type t (zp x z) (mem_fib.1 hz) (fun c => w c.1 c.2)
  · have hx : x ∈ reverseFiber t y := mem_rfib.2 h
    unfold typeReverse; rw [if_pos h]
    refine const_sum _ _ (∏ c, sourceBayesReverse p w c.2 c.1 ^ t.count c) (fun z hz => ?_) hx hpos
    exact prod_type t (zp z y) (mem_rfib.1 hz) (fun c => sourceBayesReverse p w c.2 c.1)
