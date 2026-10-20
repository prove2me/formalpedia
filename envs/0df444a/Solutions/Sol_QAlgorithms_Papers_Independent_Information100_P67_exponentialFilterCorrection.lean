-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P67.exponentialFilterCorrection
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T05:47:48.367885+00:00
-- url     : https://prove2.me/submissions/4e78a8d1-a68c-40a1-a7f1-f75e9f0c8543

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P67

noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder

open MeasureTheory Filter

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Information100 QAlgorithms.Papers.Independent.Information100.P67

lemma h54b_sqrt_add_le (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := by
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith [Real.sq_sqrt hx, Real.sq_sqrt hy, Real.sqrt_nonneg x, Real.sqrt_nonneg y]

lemma h54b_log_div : Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 1) / (n : ℝ)) atTop (nhds 0) := by
  have h := Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero
  have h2 : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have := h.comp h2
  refine this.congr (fun n => ?_)
  simp [Function.comp]

lemma h54b_logb_eq (a n : ℕ) (c : ℝ) :
    let g := postselectionFactor a n
    let delta := Real.rpow 2 (-c * n)
    let u := delta ^ 2 / 16
    let v := u ^ 2 / (32 * g)
    Real.logb 2 (2 / v ^ 2) = 27 + 2 * Real.logb 2 g + 8 * (c * n) ∧
      Real.logb 2 (1 / delta) = c * n ∧ 0 < g := by
  intro g delta u v
  have hg : 0 < g := by unfold g postselectionFactor; positivity
  have hd : 0 < delta := Real.rpow_pos_of_pos (by norm_num) _
  have h2 : (2 : ℝ) ^ (c * n) * delta = 1 := by
    unfold delta
    rw [Real.rpow_eq_pow, ← Real.rpow_add (by norm_num)]
    ring_nf; simp
  have e1 : 1 / delta = (2 : ℝ) ^ (c * n) := by
    field_simp; linarith
  have e2 : 2 / v ^ 2 = (2 : ℝ) ^ (27 : ℝ) * g ^ 2 * ((2 : ℝ) ^ (c * n)) ^ 8 := by
    have : (2 : ℝ) ^ (27 : ℝ) = 134217728 := by norm_num
    rw [this]
    unfold v u
    rw [← e1]
    field_simp
    ring
  refine ⟨?_, ?_, hg⟩
  · rw [e2, Real.logb_mul (by positivity) (by positivity), Real.logb_mul (by positivity)
      (by positivity), Real.logb_pow, Real.logb_pow, Real.logb_rpow (by norm_num) (by norm_num),
      Real.logb_rpow (by norm_num) (by norm_num)]
    push_cast; ring
  · rw [e1, Real.logb_rpow (by norm_num) (by norm_num)]

theorem solution (a d : ℕ) (ha : 0 < a) (hd : 0 < d)
    (c : ℝ) (hc : 0 < c) :
    ∀ eta : ℝ, 0 < eta → ∃ n0 : ℕ, 1 ≤ n0 ∧ ∀ n ≥ n0,
      filterDimensionCorrection a d n (Real.rpow 2 (-c * n)) / (n : ℝ) ≤
        entropyDimensionConstant d * Real.sqrt (8 * c) + 8 * c + eta := by
  intro eta heta
  set K := entropyDimensionConstant d with hK
  have hK0 : 0 ≤ K := by
    rw [hK]; unfold entropyDimensionConstant
    apply mul_nonneg (by norm_num)
    apply Real.logb_nonneg (by norm_num)
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  -- L n = logb 2 g
  set L : ℕ → ℝ := fun n => Real.logb 2 (postselectionFactor a n) with hL
  have hLeq : ∀ n : ℕ, L n = (a ^ 2 : ℕ) * (Real.log ((n : ℝ) + 1) / Real.log 2) := by
    intro n
    simp only [hL, postselectionFactor]
    rw [Real.logb_pow, Real.logb]
  have hL0 : ∀ n : ℕ, 0 ≤ L n := by
    intro n; rw [hLeq]
    apply mul_nonneg (by positivity)
    have : (0:ℝ) ≤ n := by positivity
    exact div_nonneg (Real.log_nonneg (by linarith)) (Real.log_nonneg (by norm_num))
  set e : ℕ → ℝ := fun n => (K * Real.sqrt (n * (27 + 2 * L n)) + 3 * L n + 19) / n with he
  have hLd : Tendsto (fun n : ℕ => L n / n) atTop (nhds 0) := by
    have := (h54b_log_div.const_mul (((a ^ 2 : ℕ) : ℝ) / Real.log 2))
    rw [mul_zero] at this
    refine this.congr (fun n => ?_)
    rw [hLeq]; ring
  have he0 : Tendsto e atTop (nhds 0) := by
    have hinv : Tendsto (fun n : ℕ => (1 : ℝ) / n) atTop (nhds 0) :=
      tendsto_const_div_atTop_nhds_zero_nat 1
    have t1 : Tendsto (fun n : ℕ => (27 + 2 * L n) / n) atTop (nhds 0) := by
      have := (hinv.const_mul 27).add (hLd.const_mul 2)
      simp only [mul_zero, add_zero] at this
      refine this.congr (fun n => ?_)
      ring
    have t2 : Tendsto (fun n : ℕ => K * Real.sqrt ((27 + 2 * L n) / n) + 3 * (L n / n) +
        19 * (1 / n)) atTop (nhds 0) := by
      have := ((t1.sqrt.const_mul K).add (hLd.const_mul 3)).add (hinv.const_mul 19)
      simpa using this
    refine t2.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    simp only [he]
    have : Real.sqrt (n * (27 + 2 * L n)) = n * Real.sqrt ((27 + 2 * L n) / n) := by
      rw [show (n : ℝ) * (27 + 2 * L n) = n ^ 2 * ((27 + 2 * L n) / n) by field_simp,
        Real.sqrt_mul (by positivity), Real.sqrt_sq hn'.le]
    rw [this]
    field_simp
  obtain ⟨n1, hn1⟩ := (eventually_atTop.mp (he0.eventually (gt_mem_nhds heta)))
  refine ⟨max n1 1, le_max_right _ _, fun n hn => ?_⟩
  have hn1' := hn1 n (le_trans (le_max_left _ _) hn)
  have hnpos : (0 : ℝ) < n := by
    have : 1 ≤ n := le_trans (le_max_right _ _) hn
    exact_mod_cast this
  obtain ⟨E1, E2, hg⟩ := h54b_logb_eq a n c
  unfold filterDimensionCorrection
  simp only []
  rw [E1, E2]
  have hsq : Real.sqrt (n * (27 + 2 * L n + 8 * (c * n))) ≤
      n * Real.sqrt (8 * c) + Real.sqrt (n * (27 + 2 * L n)) := by
    have := h54b_sqrt_add_le (n ^ 2 * (8 * c)) (n * (27 + 2 * L n)) (by positivity)
      (by have := hL0 n; positivity)
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hnpos.le] at this
    calc Real.sqrt (n * (27 + 2 * L n + 8 * (c * n)))
        = Real.sqrt (n ^ 2 * (8 * c) + n * (27 + 2 * L n)) := by ring_nf
      _ ≤ _ := this
  have hL' : Real.logb 2 (postselectionFactor a n) = L n := rfl
  rw [hL']
  have key : (K * Real.sqrt (n * (27 + 2 * L n + 8 * (c * n))) + 3 * L n + 8 * (c * n) + 19) ≤
      n * (K * Real.sqrt (8 * c) + 8 * c) + n * e n := by
    simp only [he]
    rw [mul_div_cancel₀ _ hnpos.ne']
    have := mul_le_mul_of_nonneg_left hsq hK0
    nlinarith
  rw [div_le_iff₀ hnpos]
  nlinarith
