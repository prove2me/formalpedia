-- Prove2me | solution 1 for ZeroOneIALM.property_1_ii
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T01:33:38.91451+00:00
-- url     : https://prove2.me/submissions/86a9deba-113e-4e61-ba51-ca26347cb0d2

import Mathlib
import Definitions.Def_ZeroOneIALM_Prox

set_option autoImplicit false

open ZeroOneIALM

namespace ZeroOneIALM.ProxProof

theorem mem_proxScalar (lam α t s : ℝ) : s ∈ proxScalar lam α t ↔
    ∀ y, lam * zeroOneLoss s + (s - t) ^ 2 / (2 * α) ≤
      lam * zeroOneLoss y + (y - t) ^ 2 / (2 * α) := by
  unfold proxScalar GenNewtonSubgrad.ProxReg.prox
  simp only [Set.mem_ofPred_eq, Real.norm_eq_abs, sq_abs]
  constructor
  · intro h y
    have := h y
    rw [← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff] at this
    exact this
  · intro h y
    rw [← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff]
    exact h y

theorem mem_proxVec {n : ℕ} (lam α : ℝ) (z u : EuclideanSpace ℝ (Fin n)) : u ∈ proxVec lam α z ↔
    ∀ y : EuclideanSpace ℝ (Fin n), lam * posCount u + ‖u - z‖ ^ 2 / (2 * α) ≤
      lam * posCount y + ‖y - z‖ ^ 2 / (2 * α) := by
  unfold proxVec GenNewtonSubgrad.ProxReg.prox
  simp only [Set.mem_ofPred_eq]
  constructor
  · intro h y
    have := h y
    rw [← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff] at this
    exact this
  · intro h y
    rw [← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff]
    exact h y

theorem obj_sum {n : ℕ} (lam α : ℝ) (z u : EuclideanSpace ℝ (Fin n)) :
    lam * posCount u + ‖u - z‖ ^ 2 / (2 * α) =
      ∑ i, (lam * zeroOneLoss (u i) + (u i - z i) ^ 2 / (2 * α)) := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  unfold posCount
  rw [Finset.mul_sum, Finset.sum_div, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp [Real.norm_eq_abs, sq_abs]

end ZeroOneIALM.ProxProof

open ZeroOneIALM.ProxProof in
theorem solution {n : ℕ} {lam α : ℝ} (hlam : 0 < lam) (hα : 0 < α) :
    (∀ z u : EuclideanSpace ℝ (Fin n),
      u ∈ proxVec lam α z ↔ ∀ i, u i ∈ proxScalar lam α (z i)) ∧
    ∀ t : ℝ,
      (t ∈ Set.Ioo 0 (Real.sqrt (2 * lam * α)) → proxScalar lam α t = {0}) ∧
      (t ∈ ({0, Real.sqrt (2 * lam * α)} : Set ℝ) → proxScalar lam α t = {0, t}) ∧
      (t ∈ Set.Iio 0 ∪ Set.Ioi (Real.sqrt (2 * lam * α)) → proxScalar lam α t = {t}) := by
  have hα2 : 0 < 2 * α := by linarith
  have l_pos : ∀ s : ℝ, 0 < s → zeroOneLoss s = 1 := fun s hs => by simp [zeroOneLoss, hs]
  have l_np : ∀ s : ℝ, s ≤ 0 → zeroOneLoss s = 0 := fun s hs => by
    simp [zeroOneLoss, not_lt.mpr hs]
  have hdiv : ∀ a b : ℝ, a / (2 * α) ≤ b / (2 * α) ↔ a ≤ b := fun a b =>
    div_le_div_iff_of_pos_right hα2
  have hdivlt : ∀ a b : ℝ, a / (2 * α) < b / (2 * α) ↔ a < b := fun a b =>
    div_lt_div_iff_of_pos_right hα2
  have hlamdiv : lam = (2 * lam * α) / (2 * α) := by field_simp
  refine ⟨?_, fun t => ⟨?_, ?_, ?_⟩⟩
  · intro z u
    rw [mem_proxVec]
    constructor
    · intro hu i
      rw [mem_proxScalar]
      intro y
      have h := hu (u + EuclideanSpace.single i (y - u i))
      rw [obj_sum, obj_sum] at h
      have hsplit : ∑ j, (lam * zeroOneLoss ((u + EuclideanSpace.single i (y - u i)) j) +
            ((u + EuclideanSpace.single i (y - u i)) j - z j) ^ 2 / (2 * α)) -
          ∑ j, (lam * zeroOneLoss (u j) + (u j - z j) ^ 2 / (2 * α)) =
          (lam * zeroOneLoss y + (y - z i) ^ 2 / (2 * α)) -
            (lam * zeroOneLoss (u i) + (u i - z i) ^ 2 / (2 * α)) := by
        rw [← Finset.sum_sub_distrib, Finset.sum_eq_single i]
        · simp
        · intro j _ hji
          simp [EuclideanSpace.single_apply, hji]
        · intro h; exact absurd (Finset.mem_univ i) h
      linarith
    · intro h y
      rw [obj_sum, obj_sum]
      exact Finset.sum_le_sum fun i _ => (mem_proxScalar _ _ _ _).mp (h i) (y i)
  · -- 0 < t < √(2λα)
    rintro ⟨ht0, htT⟩
    have ht2 : t ^ 2 < 2 * lam * α := (Real.lt_sqrt ht0.le).mp htT
    have hlt : t ^ 2 / (2 * α) < lam := by rw [hlamdiv, hdivlt]; exact ht2
    ext s
    rw [mem_proxScalar, Set.mem_singleton_iff]
    constructor
    · intro h
      have h0 := h 0
      rw [l_np 0 le_rfl] at h0
      by_contra hs
      rcases lt_or_gt_of_ne hs with hs | hs
      · rw [l_np s hs.le] at h0
        have : t ^ 2 < (s - t) ^ 2 := by nlinarith
        have := (hdivlt _ _).mpr this
        simp only [mul_zero, zero_add, zero_sub, neg_sq] at h0
        linarith
      · rw [l_pos s hs] at h0
        have : 0 ≤ (s - t) ^ 2 / (2 * α) := by positivity
        simp only [mul_zero, zero_add, zero_sub, neg_sq, mul_one] at h0
        linarith
    · rintro rfl y
      rw [l_np 0 le_rfl]
      simp only [mul_zero, zero_add, zero_sub, neg_sq]
      by_cases hy : 0 < y
      · rw [l_pos y hy]
        have : 0 ≤ (y - t) ^ 2 / (2 * α) := by positivity
        linarith
      · push Not at hy
        rw [l_np y hy, mul_zero, zero_add, hdiv]
        nlinarith
  · -- t = 0 or t = √(2λα)
    intro ht
    rcases ht with rfl | ht
    · ext s
      rw [mem_proxScalar]
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, or_self, sub_zero]
      constructor
      · intro h
        have h0 := h 0
        rw [l_np 0 le_rfl] at h0
        simp only [mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
          zero_div, add_zero] at h0
        by_contra hs
        rcases lt_or_gt_of_ne hs with hs | hs
        · rw [l_np s hs.le] at h0
          have : 0 < s ^ 2 / (2 * α) := by positivity
          linarith
        · rw [l_pos s hs] at h0
          have : 0 ≤ s ^ 2 / (2 * α) := by positivity
          linarith
      · rintro rfl y
        rw [l_np 0 le_rfl]
        have : 0 ≤ zeroOneLoss y := by unfold zeroOneLoss; split_ifs <;> norm_num
        have : 0 ≤ y ^ 2 / (2 * α) := by positivity
        simp only [mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
          zero_div, add_zero]
        nlinarith
    · rw [Set.mem_singleton_iff] at ht
      subst ht
      set T := Real.sqrt (2 * lam * α) with hT
      have hT0 : 0 < T := Real.sqrt_pos.mpr (by positivity)
      have hT2 : T ^ 2 = 2 * lam * α := Real.sq_sqrt (by positivity)
      have hTl : T ^ 2 / (2 * α) = lam := by rw [hT2]; field_simp
      ext s
      rw [mem_proxScalar]
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · intro h
        have h0 := h 0
        rw [l_np 0 le_rfl] at h0
        simp only [mul_zero, zero_add, zero_sub, neg_sq, hTl] at h0
        by_cases hs : 0 < s
        · right
          rw [l_pos s hs, mul_one] at h0
          have : (s - T) ^ 2 / (2 * α) ≤ 0 := by linarith
          have : (s - T) ^ 2 ≤ 0 := by
            have := (div_le_iff₀ hα2).mp this; linarith
          nlinarith [sq_nonneg (s - T)]
        · left
          push Not at hs
          rw [l_np s hs, mul_zero, zero_add, ← hTl, hdiv] at h0
          nlinarith
      · intro hs y
        have hval : lam * zeroOneLoss s + (s - T) ^ 2 / (2 * α) = lam := by
          rcases hs with rfl | rfl
          · rw [l_np 0 le_rfl]; simp only [mul_zero, zero_add, zero_sub, neg_sq, hTl]
          · rw [l_pos T hT0]; simp
        rw [hval]
        by_cases hy : 0 < y
        · rw [l_pos y hy, mul_one]
          have : 0 ≤ (y - T) ^ 2 / (2 * α) := by positivity
          linarith
        · push Not at hy
          rw [l_np y hy, mul_zero, zero_add, ← hTl, hdiv]
          nlinarith
  · -- t < 0 or t > √(2λα)
    intro ht
    rcases ht with ht | ht
    · rw [Set.mem_Iio] at ht
      ext s
      rw [mem_proxScalar, Set.mem_singleton_iff]
      constructor
      · intro h
        have h0 := h t
        rw [l_np t ht.le, sub_self] at h0
        simp only [mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
          zero_div, add_zero] at h0
        by_cases hs : 0 < s
        · rw [l_pos s hs] at h0
          have : 0 ≤ (s - t) ^ 2 / (2 * α) := by positivity
          linarith
        · push Not at hs
          rw [l_np s hs, mul_zero, zero_add] at h0
          have : (s - t) ^ 2 ≤ 0 := by
            have := (div_le_iff₀ hα2).mp h0; linarith
          nlinarith [sq_nonneg (s - t)]
      · rintro rfl y
        rw [l_np s ht.le, sub_self]
        have : 0 ≤ zeroOneLoss y := by unfold zeroOneLoss; split_ifs <;> norm_num
        have : 0 ≤ (y - s) ^ 2 / (2 * α) := by positivity
        simp only [mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
          zero_div, add_zero]
        nlinarith
    · rw [Set.mem_Ioi] at ht
      have hT0 : 0 < Real.sqrt (2 * lam * α) := Real.sqrt_pos.mpr (by positivity)
      have ht0 : 0 < t := hT0.trans ht
      have ht2 : 2 * lam * α < t ^ 2 := (Real.sqrt_lt' ht0).mp ht
      have hgt : lam < t ^ 2 / (2 * α) := by rw [hlamdiv, hdivlt]; exact ht2
      ext s
      rw [mem_proxScalar, Set.mem_singleton_iff]
      constructor
      · intro h
        have h0 := h t
        rw [l_pos t ht0, sub_self, mul_one] at h0
        simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div,
          add_zero] at h0
        by_cases hs : 0 < s
        · rw [l_pos s hs, mul_one] at h0
          have : (s - t) ^ 2 / (2 * α) ≤ 0 := by linarith
          have : (s - t) ^ 2 ≤ 0 := by
            have := (div_le_iff₀ hα2).mp this; linarith
          nlinarith [sq_nonneg (s - t)]
        · push Not at hs
          rw [l_np s hs, mul_zero, zero_add] at h0
          have : t ^ 2 / (2 * α) ≤ (s - t) ^ 2 / (2 * α) := by rw [hdiv]; nlinarith
          linarith
      · rintro rfl y
        rw [l_pos s ht0, sub_self, mul_one]
        simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, add_zero]
        by_cases hy : 0 < y
        · rw [l_pos y hy, mul_one]
          have : 0 ≤ (y - s) ^ 2 / (2 * α) := by positivity
          linarith
        · push Not at hy
          rw [l_np y hy, mul_zero, zero_add]
          have : s ^ 2 / (2 * α) ≤ (y - s) ^ 2 / (2 * α) := by rw [hdiv]; nlinarith
          linarith
