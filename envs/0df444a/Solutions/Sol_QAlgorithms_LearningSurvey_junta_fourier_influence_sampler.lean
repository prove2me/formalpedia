-- Prove2me | solution 1 for QAlgorithms.LearningSurvey.junta_fourier_influence_sampler
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T23:11:48.299842+00:00
-- url     : https://prove2.me/submissions/9c57fbf5-f334-49a8-9825-ca2ade8a353f

import Theorems.Thm_QAlgorithms_LearningSurvey_hadamard_influence_sampling
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open scoped BigOperators
open QAlgorithms QAlgorithms.LearningSurvey

namespace JuntaResampling
open Classical

private def mix {n : ℕ} (A : Finset (Fin n)) (x y : Qubits n) : Qubits n :=
  fun i => if i ∈ A then y i else x i

private def swap {n : ℕ} (A : Finset (Fin n)) : (Qubits n × Qubits n) ≃ (Qubits n × Qubits n) where
  toFun p := (mix A p.1 p.2, mix A p.2 p.1)
  invFun p := (mix A p.1 p.2, mix A p.2 p.1)
  left_inv p := by ext i <;> simp [mix] <;> split_ifs <;> rfl
  right_inv p := by ext i <;> simp [mix] <;> split_ifs <;> rfl

private lemma mix_empty {n : ℕ} (x y : Qubits n) : mix ∅ x y = x := by
  funext i; simp [mix]

private def agree {n : ℕ} (W : Qubits n) (x y : Qubits n) : Prop :=
  ∀ i, W i = true → y i = x i

private lemma agree_mix {n : ℕ} (W : Qubits n) (A : Finset (Fin n)) (x y : Qubits n) :
    agree W (mix A x y) (mix A y x) ↔ agree W x y := by
  constructor <;> intro h i hi <;> have hh := h i hi
  all_goals by_cases ha : i ∈ A <;> simpa [mix, ha, eq_comm] using hh

private lemma mask_card {n : ℕ} (W : Qubits n) (x : Qubits n) :
    (∑ y : Qubits n, if agree W x y then (1:ℝ) else 0) * (2:ℝ)^hammingWeight W = (2:ℝ)^n := by
  classical
  let E : {y : Qubits n // agree W x y} ≃ ({i : Fin n // W i = false} → Bool) :=
    { toFun := fun y i => y.1 i.1
      invFun := fun g => ⟨fun i => if h : W i = true then x i else g ⟨i, by cases hi : W i <;> simp_all⟩,
        by intro i hi; simp [hi]⟩
      left_inv := by
        intro y; apply Subtype.ext; funext i
        dsimp only
        split_ifs with h
        · exact (y.2 i h).symm
        · rfl
      right_inv := by intro g; funext i; simp [i.2] }
  have hc : Fintype.card {i : Fin n // W i = false} + hammingWeight W = n := by
    have h := Finset.card_filter_add_card_filter_not (s:=Finset.univ) (p:=fun i : Fin n => W i = true)
    have hf : (Finset.univ.filter fun i : Fin n => ¬ W i = true) =
        (Finset.univ.filter fun i => W i = false) := by
      ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; cases W i <;> decide
    rw [hf] at h
    simpa only [hammingWeight, Fintype.card_subtype, Finset.card_univ, Fintype.card_fin, add_comm] using h
  have hs : (∑ y : Qubits n, if agree W x y then (1:ℝ) else 0) =
      (2:ℝ)^Fintype.card {i : Fin n // W i = false} := by
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one, ← Fintype.card_subtype]
    rw [Fintype.card_congr E, Fintype.card_fun]
    norm_num
  rw [hs, ← pow_add, hc]

private lemma mixed_sum {n : ℕ} (W : Qubits n) (A : Finset (Fin n)) (g : Qubits n → ℝ) :
    (∑ x : Qubits n, ∑ y : Qubits n, if agree W x y then g (mix A x y) else 0) *
        (2:ℝ)^hammingWeight W = (2:ℝ)^n * ∑ x, g x := by
  classical
  have he := Equiv.sum_comp (swap A) (fun p : Qubits n × Qubits n =>
    if agree W p.1 p.2 then g p.1 else 0)
  simp only [Fintype.sum_prod_type, swap, Equiv.coe_fn_mk, agree_mix] at he
  rw [he]
  have hid (x : Qubits n) :
      (∑ y : Qubits n, if agree W x y then g x else 0) =
      g x * (∑ y : Qubits n, if agree W x y then (1:ℝ) else 0) := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro y _; split_ifs <;> simp
  simp_rw [hid]
  rw [Finset.sum_mul]
  simp_rw [mul_assoc, mask_card]
  rw [← Finset.sum_mul, mul_comm]

private def edge {n : ℕ} (f : Qubits n → Bool) (i : Fin n) (x : Qubits n) : ℝ :=
  if f (Function.update x i (!x i)) ≠ f x then 1 else 0

private lemma edge_nonneg {n : ℕ} (f : Qubits n → Bool) (i : Fin n) (x : Qubits n) :
    0 ≤ edge f i x := by unfold edge; split_ifs <;> norm_num

private lemma path_bound {n : ℕ} (f : Qubits n → Bool) (A : Finset (Fin n)) :
    ∃ E : (Qubits n × Qubits n) → ℝ,
      (∀ x y, (if f (mix A x y) ≠ f x then (1:ℝ) else 0) ≤ E (x,y)) ∧
      ∀ W : Qubits n,
        (∑ x, ∑ y, if agree W x y then E (x,y) else 0) * (2:ℝ)^hammingWeight W =
          (2:ℝ)^n * ∑ i ∈ A, ∑ x, edge f i x := by
  classical
  induction A using Finset.induction_on with
  | empty =>
    refine ⟨fun _ => 0, ?_, ?_⟩
    · intro x y; simp [mix_empty]
    · intro W; simp
  | @insert i A hi ih =>
    obtain ⟨E,hE,hSum⟩ := ih
    refine ⟨fun p => E p + edge f i (mix A p.1 p.2), ?_, ?_⟩
    · intro x y
      have ht : (if f (mix (insert i A) x y) ≠ f x then (1:ℝ) else 0) ≤
          (if f (mix A x y) ≠ f x then (1:ℝ) else 0) + edge f i (mix A x y) := by
        have hm : mix (insert i A) x y = Function.update (mix A x y) i (y i) := by
          funext j; by_cases hj : j = i
          · subst j; simp [mix]
          · simp [mix, hj]
        have hb : y i = (mix A x y) i ∨ y i = !(mix A x y) i := by
          cases y i <;> cases (mix A x y) i <;> simp
        rcases hb with hb | hb
        · rw [hm, hb, Function.update_eq_self]; have := edge_nonneg f i (mix A x y); linarith
        · rw [hm, hb]
          unfold edge
          split_ifs <;> simp_all
      exact ht.trans (add_le_add (hE x y) le_rfl)
    · intro W
      have hid (x y : Qubits n) :
          (if agree W x y then E (x,y) + edge f i (mix A x y) else 0) =
          (if agree W x y then E (x,y) else 0) +
          (if agree W x y then edge f i (mix A x y) else 0) := by split_ifs <;> simp
      simp_rw [hid, Finset.sum_add_distrib]
      rw [add_mul, hSum W, mixed_sum W A (edge f i), Finset.sum_insert hi, mul_add]
      ring

lemma resampling {n : ℕ} (f : Qubits n → Bool) (S : Finset (Fin n))
    (hS : ∀ x y : Qubits n, (∀ i ∈ S, x i = y i) → f x = f y)
    (W : Qubits n) :
    (((2 : ℝ)^n)⁻¹ * ∑ x : Qubits n,
      (((2 : ℝ)^n)⁻¹ * ∑ y : Qubits n,
        if (∀ i, W i = true → y i = x i) ∧ f y ≠ f x then (1 : ℝ) else 0) *
      (2 : ℝ)^hammingWeight W) ≤
    ∑ i ∈ S, if W i = true then 0 else
      ((2 : ℝ)^n)⁻¹ * ∑ x : Qubits n,
        if f (Function.update x i (!x i)) ≠ f x then (1 : ℝ) else 0 := by
  classical
  let A := S.filter (fun i => W i ≠ true)
  obtain ⟨E,hE,hSum⟩ := path_bound f A
  have hp (x y : Qubits n) :
      (if agree W x y ∧ f y ≠ f x then (1:ℝ) else 0) ≤
      if agree W x y then E (x,y) else 0 := by
    by_cases h : agree W x y
    · have he : f (mix A x y) = f y := by
        apply hS
        intro i hi
        by_cases hw : W i = true
        · simpa [mix, A, hw] using (h i hw).symm
        · simp [mix, A, hi, hw]
      simpa only [h, true_and, if_true, he] using hE x y
    · simp [h]
  have hbound := mul_le_mul_of_nonneg_right
    (Finset.sum_le_sum fun x (_ : x ∈ Finset.univ) =>
      Finset.sum_le_sum fun y (_ : y ∈ Finset.univ) => hp x y)
    (show 0 ≤ (2:ℝ)^hammingWeight W by positivity)
  rw [hSum W] at hbound
  have hpos : 0 < (2:ℝ)^n := by positivity
  have rhs : (∑ i ∈ S, if W i = true then (0:ℝ) else
      ((2:ℝ)^n)⁻¹ * ∑ x, edge f i x) =
      ((2:ℝ)^n)⁻¹ * ∑ i ∈ A, ∑ x, edge f i x := by
    rw [Finset.mul_sum, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hw : W i = true <;> simp [hw]
  change _ ≤ ∑ i ∈ S, if W i = true then 0 else ((2:ℝ)^n)⁻¹ * ∑ x, edge f i x
  rw [rhs]
  simp only [← Finset.mul_sum, ← Finset.sum_mul]
  calc
    _ = ((2:ℝ)^n)⁻¹ * ((2:ℝ)^n)⁻¹ *
        ((∑ x : Qubits n, ∑ y : Qubits n,
          if (∀ i, W i = true → y i = x i) ∧ f y ≠ f x then (1:ℝ) else 0) *
            (2:ℝ)^hammingWeight W) := by ring
    _ ≤ ((2:ℝ)^n)⁻¹ * ((2:ℝ)^n)⁻¹ * ((2:ℝ)^n * ∑ i ∈ A, ∑ x, edge f i x) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      calc
        _ = (∑ x : Qubits n, ∑ y : Qubits n,
            if agree W x y ∧ f y ≠ f x then (1:ℝ) else 0) * (2:ℝ)^hammingWeight W := by
          congr 1
          apply Finset.sum_congr rfl
          intro x _
          apply Finset.sum_congr rfl
          intro y _
          by_cases h : agree W x y ∧ f y ≠ f x
          · rw [if_pos h]
            have hraw : (∀ i, W i = true → y i = x i) ∧ f y ≠ f x := h
            exact if_pos hraw
          · rw [if_neg h]
            have hraw : ¬ ((∀ i, W i = true → y i = x i) ∧ f y ≠ f x) := h
            exact if_neg hraw
        _ ≤ _ := hbound
    _ = _ := by field_simp

end JuntaResampling

private lemma influence_bounds {n : ℕ} (f : Qubits n → Bool) (i : Fin n) :
    0 ≤ (((2:ℝ)^n)⁻¹ * ∑ x : Qubits n, if f (Function.update x i (!x i)) ≠ f x then (1:ℝ) else 0) ∧
    (((2:ℝ)^n)⁻¹ * ∑ x : Qubits n, if f (Function.update x i (!x i)) ≠ f x then (1:ℝ) else 0) ≤ 1 := by
  constructor
  · positivity
  · have hs : (∑ x : Qubits n, if f (Function.update x i (!x i)) ≠ f x then (1:ℝ) else 0) ≤ (2:ℝ)^n := by
      calc
        _ ≤ ∑ _x : Qubits n, (1:ℝ) := Finset.sum_le_sum fun x _ => by split_ifs <;> norm_num
        _ = _ := by simp [Qubits]
    calc
      _ ≤ ((2:ℝ)^n)⁻¹ * (2:ℝ)^n := mul_le_mul_of_nonneg_left hs (by positivity)
      _ = 1 := inv_mul_cancel₀ (by positivity)

private lemma influence_outside {n : ℕ} (f : Qubits n → Bool) (S : Finset (Fin n))
    (hS : ∀ x y : Qubits n, (∀ i ∈ S, x i = y i) → f x = f y)
    (i : Fin n) (hi : i ∉ S) :
    (((2:ℝ)^n)⁻¹ * ∑ x : Qubits n, if f (Function.update x i (!x i)) ≠ f x then (1:ℝ) else 0) = 0 := by
  have he (x : Qubits n) : f (Function.update x i (!x i)) = f x := by
    apply hS
    intro j hj
    have hji : j ≠ i := by intro h; subst j; exact hi hj
    simp [hji]
  simp [he]

theorem solution (n T : ℕ) (_hT : 0 < T) :
    ∃ c : QAlgorithms.Circuit QAlgorithms.htcxGateSet (T * (n + 1) + 0),
      c.size ≤ T * (n + 1) ∧
      ∀ (f : QAlgorithms.Qubits n → Bool) (S : Finset (Fin n)),
        (∀ x y : QAlgorithms.Qubits n, (∀ i ∈ S, x i = y i) → f x = f y) →
        let P := fun z => QAlgorithms.prob
          (QAlgorithms.act c.unitary (QAlgorithms.LearningSurvey.juntaExamplesState n T 0 f)) z
        let V := fun z i => decide (∃ j : Fin T, QAlgorithms.LearningSurvey.exInput n z j i = true)
        let I := fun i : Fin n => ((2 : ℝ)^n)⁻¹ * ∑ x : QAlgorithms.Qubits n,
          if f (Function.update x i (!x i)) ≠ f x then (1 : ℝ) else 0
        (∑ z, P z) = 1 ∧
        (∀ z, P z ≠ 0 → ∀ i, V z i = true → i ∈ S) ∧
        (∀ i ∈ S, 0 ≤ I i ∧ I i ≤ 1 ∧
          (∑ z, if V z i = false then P z else 0) ≤ (1 - I i / 2)^T) ∧
        (∀ W : QAlgorithms.Qubits n,
          (((2 : ℝ)^n)⁻¹ * ∑ x : QAlgorithms.Qubits n,
            (((2 : ℝ)^n)⁻¹ * ∑ y : QAlgorithms.Qubits n,
              if (∀ i, W i = true → y i = x i) ∧ f y ≠ f x then (1 : ℝ) else 0) *
            (2 : ℝ)^QAlgorithms.hammingWeight W) ≤
          ∑ i ∈ S, if W i = true then 0 else I i) := by
  obtain ⟨c,hsize,hc⟩ := hadamard_influence_sampling n T
  refine ⟨c,hsize,?_⟩
  intro f S hS
  let P := fun z => prob (act c.unitary (juntaExamplesState n T 0 f)) z
  let V := fun (z : Qubits (T*(n+1)+0)) (i : Fin n) => decide (∃ j : Fin T, exInput n z j i = true)
  let I := fun i : Fin n => ((2:ℝ)^n)⁻¹ * ∑ x : Qubits n,
    if f (Function.update x i (!x i)) ≠ f x then (1:ℝ) else 0
  change (∑ z, P z) = 1 ∧ _
  obtain ⟨hnorm,habs⟩ := hc f
  have hp (z) : 0 ≤ P z := by dsimp [P, prob]; positivity
  have hv (z : Qubits (T*(n+1)+0)) (i : Fin n) :
      V z i = false ↔ ∀ j : Fin T, exInput n z j i = false := by
    simp only [V, decide_eq_false_iff_not, not_exists]
    apply forall_congr'; intro j; cases exInput n z j i <;> decide
  have htail (i : Fin n) : (∑ z, if V z i = false then P z else 0) = (1-I i/2)^T := by
    simpa only [hv] using habs i
  refine ⟨hnorm, ?_, ?_, fun W => JuntaResampling.resampling f S hS W⟩
  · intro z hz i hvi
    by_contra hi
    have hzI : I i = 0 := influence_outside f S hS i hi
    have hzero : (∑ z, if V z i = true then P z else 0) = 0 := by
      have hs : (∑ z, if V z i = true then P z else 0) +
          (∑ z, if V z i = false then P z else 0) = ∑ z, P z := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro z _; cases V z i <;> simp
      rw [hnorm, htail, hzI] at hs
      simpa using hs
    have hle : (if V z i = true then P z else 0) ≤ ∑ z, if V z i = true then P z else 0 :=
      Finset.single_le_sum (f := fun z => if V z i = true then P z else 0)
        (fun z _ => by split_ifs <;> simp [hp z]) (Finset.mem_univ z)
    have hvi' : V z i = true := by simpa only [V, decide_eq_true_eq] using hvi
    have hle' : P z ≤ 0 := by
      calc
        P z = (if V z i = true then P z else 0) := (if_pos hvi').symm
        _ ≤ ∑ z, if V z i = true then P z else 0 := hle
        _ = 0 := hzero
    exact hz (le_antisymm hle' (hp z))
  · intro i _hi
    obtain ⟨h0,h1⟩ := influence_bounds f i
    exact ⟨h0,h1,(htail i).le⟩
