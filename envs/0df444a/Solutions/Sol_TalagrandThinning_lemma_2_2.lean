-- Prove2me | solution 1 for TalagrandThinning.lemma_2_2
-- status  : ACCEPTED   (prove)
-- author  : @jdenwood
-- created : 2026-11-23T06:41:01.61568+00:00
-- url     : https://prove2.me/submissions/be623d22-0372-49dd-9ce9-ef1288102cf7

import Mathlib
import Definitions.Def_TalagrandThinning_liftL

set_option autoImplicit false

namespace TTL22
open TalagrandThinning

theorem beta_eq (t p : ℝ) (ht0 : 0 < t) (ht1 : t < 1) (hp0 : 0 < p) (hp1 : p < 1) :
    beta t p = Real.sqrt (t * (1 - t)) * Real.sqrt (p * (1 - p)) / (p * (1 - t)) := by
  have h1 : (0:ℝ) < 1 - t := by linarith
  have h2 : (0:ℝ) < 1 - p := by linarith
  have hq : 0 < p * (1 - t) := mul_pos hp0 h1
  unfold beta
  rw [eq_div_iff hq.ne', ← Real.sqrt_mul (by positivity)]
  have e : Real.sqrt (t * (1 - p) / (p * (1 - t))) * (p * (1 - t)) =
      Real.sqrt (t * (1 - p) / (p * (1 - t)) * (p * (1 - t)) ^ 2) := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hq.le]
  rw [e]
  congr 1
  field_simp

theorem kernelH_eq (t p : ℝ) (ht0 : 0 < t) (ht1 : t < 1) (hp0 : 0 < p) (hp1 : p < 1)
    (x w : Bool) : kernelH t p x w =
      1 + ((if x then 1 else 0) - t) * ((if w then 1 else 0) - p) / (p * (1 - t)) := by
  have h1 : (0:ℝ) < 1 - t := by linarith
  have h2 : (0:ℝ) < 1 - p := by linarith
  have st : 0 < Real.sqrt (t * (1 - t)) := Real.sqrt_pos.mpr (by positivity)
  have sp : 0 < Real.sqrt (p * (1 - p)) := Real.sqrt_pos.mpr (by positivity)
  unfold kernelH phi
  rw [beta_eq t p ht0 ht1 hp0 hp1]
  field_simp

theorem h10 (t p : ℝ) (ht0 : 0 < t) (ht1 : t < 1) (hp0 : 0 < p) (hp1 : p < 1) :
    kernelH t p true false = 0 := by
  have h1 : (1:ℝ) - t ≠ 0 := by linarith
  rw [kernelH_eq t p ht0 ht1 hp0 hp1]; simp; field_simp; ring

theorem hmean (t p : ℝ) (ht0 : 0 < t) (ht1 : t < 1) (hp0 : 0 < p) (hp1 : p < 1) (x : Bool) :
    (1 - p) * kernelH t p x false + p * kernelH t p x true = 1 := by
  have h1 : (1:ℝ) - t ≠ 0 := by linarith
  have hp : p ≠ 0 := hp0.ne'
  rw [kernelH_eq t p ht0 ht1 hp0 hp1, kernelH_eq t p ht0 ht1 hp0 hp1]
  cases x <;> simp <;> field_simp <;> ring

end TTL22

open TalagrandThinning in
theorem solution {N : ℕ} (t p : ℝ) (ht0 : 0 < t) (ht1 : t < 1) (hp0 : 0 < p) (hp1 : p < 1) :
    (∀ j x w : Cube N, ¬ (j ⊓ x ≤ w) → kernelK t p j x w = 0) ∧
    (∀ j x : Cube N, liftL t p j (fun _ => 1) x = 1) := by
  constructor
  · intro j x w h
    rw [Pi.le_def] at h
    push Not at h
    obtain ⟨i, hi⟩ := h
    simp only [Pi.inf_apply] at hi
    have key : j i = true ∧ x i = true ∧ w i = false := by
      revert hi; cases j i <;> cases x i <;> cases w i <;> decide
    obtain ⟨hj, hx, hw⟩ := key
    unfold kernelK
    apply Finset.prod_eq_zero (i := i) (by simp [hj])
    rw [hx, hw]; exact TTL22.h10 t p ht0 ht1 hp0 hp1
  · intro j x
    unfold liftL expect kernelK weight
    let g : Fin N → Bool → ℝ := fun i b =>
      (if b then p else 1 - p) * (if j i = true then kernelH t p (x i) b else 1)
    have hrw : ∀ w : Cube N,
        (∏ i, if w i then p else 1 - p) *
          ((∏ i ∈ Finset.univ.filter (fun i => j i = true), kernelH t p (x i) (w i)) * 1)
        = ∏ i, g i (w i) := by
      intro w
      rw [mul_one, Finset.prod_filter, ← Finset.prod_mul_distrib]
    rw [Finset.sum_congr rfl (fun w _ => hrw w)]
    rw [← Fintype.prod_sum (fun i b => g i b)]
    apply Finset.prod_eq_one
    intro i _
    rw [Fintype.sum_bool]
    simp only [g]
    by_cases hji : j i = true
    · simp only [hji, if_true, Bool.false_eq_true, if_false]
      have := TTL22.hmean t p ht0 ht1 hp0 hp1 (x i)
      linarith
    · simp only [hji]; simp
