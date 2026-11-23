-- Prove2me | solution 1 for TalagrandThinning.lemma_3_1
-- status  : ACCEPTED   (prove)
-- author  : @jdenwood
-- created : 2026-11-23T06:33:54.290117+00:00
-- url     : https://prove2.me/submissions/7f263626-d830-41d8-b50c-116764480c93

import Mathlib
import Definitions.Def_TalagrandThinning_liftL

set_option autoImplicit false

namespace TTL31

open TalagrandThinning

lemma beta_eq (t p : ℝ) (ht0 : 0 < t) (ht1 : t < 1) (hp0 : 0 < p) (hp1 : p < 1) :
    beta t p = Real.sqrt (t * (1 - t)) * Real.sqrt (p * (1 - p)) / (p * (1 - t)) := by
  have h1 : 0 < 1 - t := by linarith
  have h2 : 0 < 1 - p := by linarith
  have hpos : 0 ≤ Real.sqrt (t * (1 - t)) * Real.sqrt (p * (1 - p)) / (p * (1 - t)) := by
    positivity
  rw [beta, ← Real.sqrt_sq hpos]
  congr 1
  rw [div_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
  field_simp

lemma prod_eq (t p : ℝ) (ht0 : 0 < t) (ht1 : t < 1) (hp0 : 0 < p) (hp1 : p < 1) (x w : Bool) :
    beta t p * phi t x * phi p w
      = ((if x then 1 else 0) - t) * ((if w then 1 else 0) - p) / (p * (1 - t)) := by
  have h1 : 0 < 1 - t := by linarith
  have h2 : 0 < 1 - p := by linarith
  have s1 : 0 < Real.sqrt (t * (1 - t)) := Real.sqrt_pos.2 (by positivity)
  have s2 : 0 < Real.sqrt (p * (1 - p)) := Real.sqrt_pos.2 (by positivity)
  rw [beta_eq t p ht0 ht1 hp0 hp1, phi, phi]
  field_simp

lemma h_true_false (t p : ℝ) (ht0 : 0 < t) (ht1 : t < 1) (hp0 : 0 < p) (hp1 : p < 1) :
    kernelH t p true false = 0 := by
  have h1 : 0 < 1 - t := by linarith
  rw [kernelH, prod_eq t p ht0 ht1 hp0 hp1]
  simp
  field_simp
  ring

lemma h_avg (t p : ℝ) (ht0 : 0 < t) (ht1 : t < 1) (hp0 : 0 < p) (hp1 : p < 1) (x : Bool) :
    (1 - p) * kernelH t p x false + p * kernelH t p x true = 1 := by
  have h1 : 0 < 1 - t := by linarith
  rw [kernelH, kernelH, prod_eq t p ht0 ht1 hp0 hp1, prod_eq t p ht0 ht1 hp0 hp1]
  simp
  field_simp
  ring

lemma kernelK_eq {N : ℕ} (t p : ℝ) (j x w : Cube N) :
    kernelK t p j x w = ∏ i, if j i then kernelH t p (x i) (w i) else 1 := by
  rw [kernelK, Finset.prod_filter]

lemma kernelK_zero {N : ℕ} (t p : ℝ) (ht0 : 0 < t) (ht1 : t < 1) (hp0 : 0 < p) (hp1 : p < 1)
    (j x w : Cube N) (h : ¬ (j ⊓ x ≤ w)) : kernelK t p j x w = 0 := by
  rw [kernelK_eq]
  have : ∃ i, j i = true ∧ x i = true ∧ w i = false := by
    by_contra hc
    apply h
    intro i
    have := fun h1 h2 h3 => hc ⟨i, h1, h2, h3⟩
    cases hj : j i <;> cases hx : x i <;> cases hw : w i <;> simp_all
  obtain ⟨i, hj, hx, hw⟩ := this
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  rw [hj, hx, hw]
  simpa using h_true_false t p ht0 ht1 hp0 hp1

lemma liftL_one {N : ℕ} (t p : ℝ) (ht0 : 0 < t) (ht1 : t < 1) (hp0 : 0 < p) (hp1 : p < 1)
    (j x : Cube N) : liftL t p j (fun _ => (1 : ℝ)) x = 1 := by
  unfold liftL expect
  simp_rw [kernelK_eq, weight, mul_one, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i (b : Bool) =>
    (if b then p else 1 - p) * (if j i then kernelH t p (x i) b else 1))]
  apply Finset.prod_eq_one
  intro i _
  rw [Fintype.sum_bool]
  by_cases hj : j i
  · simp only [hj, if_true, Bool.false_eq_true, if_false]
    linarith [h_avg t p ht0 ht1 hp0 hp1 (x i)]
  · simp [hj]

end TTL31

open TalagrandThinning in
theorem solution {N : ℕ} (t p : ℝ) (ht0 : 0 < t) (ht1 : t < 1) (hp0 : 0 < p) (hp1 : p < 1)
    (U : Set (Cube N)) (hU : IsUpperSet U) (j x : Cube N) :
    U.indicator (fun _ => (1 : ℝ)) (j ⊓ x) ≤
      (liftL t p j (U.indicator (fun _ => (1 : ℝ))) x) ^ 2 := by
  by_cases hm : j ⊓ x ∈ U
  · have : liftL t p j (U.indicator (fun _ => (1 : ℝ))) x = liftL t p j (fun _ => (1 : ℝ)) x := by
      unfold liftL expect
      apply Finset.sum_congr rfl
      intro w _
      show weight p w * (kernelK t p j x w * _) = weight p w * (kernelK t p j x w * 1)
      by_cases hw : j ⊓ x ≤ w
      · rw [Set.indicator_of_mem (hU hw hm)]
      · rw [TTL31.kernelK_zero t p ht0 ht1 hp0 hp1 j x w hw]; simp
    rw [this, TTL31.liftL_one t p ht0 ht1 hp0 hp1, Set.indicator_of_mem hm]
    norm_num
  · rw [Set.indicator_of_notMem hm]
    positivity
