-- Prove2me | solution 1 for OffGridStorage.TechChoice.eq_25_marginal_storage
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:47:39.628477+00:00
-- url     : https://prove2.me/submissions/98abe081-4261-4bae-96ce-0f99806b8639

import Mathlib
import Definitions.Def_OffGridStorage_TechChoice_Model
set_option autoImplicit false

open OffGridStorage.TechChoice

lemma ccog_I_le (a Q : ℝ) (hQ : 0 ≤ Q) (h : Q ≤ a) :
    ∫ v in Set.Icc (0:ℝ) 1, min (Q * v) a = Q / 2 := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
  have : Set.EqOn (fun v : ℝ => min (Q * v) a) (fun v => Q * v) (Set.uIcc 0 1) := by
    intro v hv
    rw [Set.uIcc_of_le zero_le_one] at hv
    simp only
    apply min_eq_left
    nlinarith [hv.1, hv.2]
  rw [intervalIntegral.integral_congr this, intervalIntegral.integral_const_mul, integral_id]
  ring

lemma ccog_I_ge (a Q : ℝ) (ha : 0 < a) (h : a ≤ Q) :
    ∫ v in Set.Icc (0:ℝ) 1, min (Q * v) a = a - a ^ 2 / (2 * Q) := by
  have hQ : 0 < Q := lt_of_lt_of_le ha h
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
  have hc0 : 0 ≤ a / Q := by positivity
  have hc1 : a / Q ≤ 1 := by rw [div_le_one hQ]; exact h
  have hcont : Continuous (fun v : ℝ => min (Q * v) a) := by fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := a / Q)
    (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)]
  have e1 : Set.EqOn (fun v : ℝ => min (Q * v) a) (fun v => Q * v) (Set.uIcc 0 (a / Q)) := by
    intro v hv
    rw [Set.uIcc_of_le hc0] at hv
    simp only
    apply min_eq_left
    have := hv.2
    rw [le_div_iff₀ hQ] at this
    nlinarith
  have e2 : Set.EqOn (fun v : ℝ => min (Q * v) a) (fun _ => a) (Set.uIcc (a / Q) 1) := by
    intro v hv
    rw [Set.uIcc_of_le hc1] at hv
    simp only
    apply min_eq_right
    have := hv.1
    rw [div_le_iff₀ hQ] at this
    nlinarith
  rw [intervalIntegral.integral_congr e1, intervalIntegral.integral_congr e2,
    intervalIntegral.integral_const_mul, integral_id, intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  field_simp
  ring

lemma ccog_profit0 (p : Params) (Q : ℝ) (he : 0 < p.e) :
    profitF p Q 0 = (p.T : ℝ) * (p.g * (∫ v in Set.Icc (0:ℝ) 1, min (Q * v) p.DH) - p.cQ * Q) := by
  unfold profitF
  have : ∫ v in Set.Icc (0:ℝ) 1, (min (Q * v) p.DH + min (p.e * pos (Q * v - p.DH)) 0)
      = ∫ v in Set.Icc (0:ℝ) 1, min (Q * v) p.DH := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
    intro v _
    simp only
    have : min (p.e * pos (Q * v - p.DH)) 0 = 0 := by
      apply min_eq_right
      exact mul_nonneg he.le (le_max_left _ _)
    rw [this]; ring
  rw [this]
  ring

lemma ccog_deriv (p : Params) (hp : Standing p) (Q K : ℝ) (hQ : 0 < Q) :
    HasDerivAt (fun K' => closedFormF p Q K')
      ((p.T : ℝ) * (p.g / Q * (-p.DH - K / p.e) + p.g - p.cK / p.e)) K := by
  have he : p.e ≠ 0 := hp.2.2.1.ne'
  have h1 : HasDerivAt (fun K' : ℝ => K' ^ 2) (2 * K) K := by
    simpa using hasDerivAt_pow 2 K
  have h2 : HasDerivAt (fun K' : ℝ => K') 1 K := hasDerivAt_id K
  have h3 : HasDerivAt (fun K' : ℝ => p.g / Q * (-p.DH ^ 2 / 2 - K' ^ 2 / (2 * p.e) - K' * p.DH)
      + p.g * (p.DH + K') - p.cK / p.e * K' - p.cQ * Q)
      (p.g / Q * (0 - (2 * K) / (2 * p.e) - 1 * p.DH) + p.g * (0 + 1) - p.cK / p.e * 1 - 0) K := by
    have a1 : HasDerivAt (fun K' : ℝ => K' ^ 2 / (2 * p.e)) ((2 * K) / (2 * p.e)) K := h1.div_const _
    have a2 : HasDerivAt (fun K' : ℝ => K' * p.DH) (1 * p.DH) K := h2.mul_const _
    have a3 : HasDerivAt (fun K' : ℝ => -p.DH ^ 2 / 2 - K' ^ 2 / (2 * p.e) - K' * p.DH)
        (0 - (2 * K) / (2 * p.e) - 1 * p.DH) K :=
      ((hasDerivAt_const K (-p.DH ^ 2 / 2)).sub a1).sub a2
    have a4 := a3.const_mul (p.g / Q)
    have a5 : HasDerivAt (fun K' : ℝ => p.g * (p.DH + K')) (p.g * (0 + 1)) K :=
      ((hasDerivAt_const K p.DH).add h2).const_mul p.g
    have a6 : HasDerivAt (fun K' : ℝ => p.cK / p.e * K') (p.cK / p.e * 1) K := h2.const_mul _
    exact ((a4.add a5).sub a6).sub_const _ |>.congr_deriv (by ring)
  have := h3.const_mul (p.T : ℝ)
  unfold closedFormF
  refine this.congr_deriv ?_
  field_simp
  ring

theorem solution (p : Params) (hp : Standing p) :
    (0 ≤ Q0 p ∧ ∀ Q : ℝ, 0 ≤ Q → profitF p Q 0 ≤ profitF p (Q0 p) 0) ∧
    (∀ Q K : ℝ, 0 < Q →
      HasDerivAt (fun K' => closedFormF p Q K')
        ((p.T : ℝ) * (p.g / Q * (-p.DH - K / p.e) + p.g - p.cK / p.e)) K) ∧
    HasDerivAt (fun K' => closedFormF p (Q0 p) K')
      ((p.T : ℝ) * (-Real.sqrt (2 * p.cQ * p.g) + p.g - p.cK / p.e)) 0 := by
  obtain ⟨hDH, hDL, he, he1, hcQ, hcK, hg, hT⟩ := hp
  have hpp : Standing p := ⟨hDH, hDL, he, he1, hcQ, hcK, hg, hT⟩
  set a := p.DH with ha
  set c := p.cQ with hc
  set g := p.g with hgdef
  have hg0 : 0 < g := by linarith
  have hgc : 0 < g / (2 * c) := by positivity
  set s := Real.sqrt (g / (2 * c)) with hs
  have hs2 : s ^ 2 = g / (2 * c) := Real.sq_sqrt hgc.le
  have hs0 : 0 < s := Real.sqrt_pos.2 hgc
  have hgs : g = 2 * c * s ^ 2 := by rw [hs2]; field_simp
  have hs1 : 1 < s := by
    by_contra hcon
    push_neg at hcon
    have h1 : s ^ 2 ≤ 1 := by nlinarith
    have h2 : 2 * c * s ^ 2 ≤ 2 * c := by nlinarith
    linarith
  have hQ0 : Q0 p = a * s := by
    unfold Q0
    rfl
  have hsq : Real.sqrt (2 * c * g) = 2 * c * s := by
    rw [hgs]
    have : 2 * c * (2 * c * s ^ 2) = (2 * c * s) ^ 2 := by ring
    rw [this, Real.sqrt_sq (by positivity)]
  have hQ0pos : 0 < Q0 p := by rw [hQ0]; positivity
  refine ⟨⟨hQ0pos.le, ?_⟩, fun Q K hQ => ccog_deriv p hpp Q K hQ, ?_⟩
  · intro Q hQ
    rw [ccog_profit0 p Q he, ccog_profit0 p (Q0 p) he]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    have hI0 : ∫ v in Set.Icc (0:ℝ) 1, min (Q0 p * v) a = a - a ^ 2 / (2 * Q0 p) :=
      ccog_I_ge a (Q0 p) hDH (by rw [hQ0]; nlinarith)
    rw [hI0, hQ0]
    rcases le_total Q a with hle | hge
    · rw [ccog_I_le a Q hQ hle]
      have : Q * (g / 2 - c) ≤ a * (g / 2 - c) := by
        apply mul_le_mul_of_nonneg_right hle; nlinarith
      have e2 : a * s * 1 = a * s := by ring
      have key : g * (a - a ^ 2 / (2 * (a * s))) - c * (a * s) = 2 * c * a * s * (s - 1) := by
        rw [hgs]; field_simp; ring
      rw [key]
      have : g * (Q / 2) - c * Q = Q * (g / 2 - c) := by ring
      rw [this]
      have h3 : a * (g / 2 - c) = c * a * (s ^ 2 - 1) := by rw [hgs]; ring
      have h4 : c * a * (s ^ 2 - 1) ≤ 2 * c * a * s * (s - 1) := by
        have : 0 < c * a := by positivity
        nlinarith [mul_pos this (sub_pos.2 hs1)]
      linarith
    · have hQp : 0 < Q := lt_of_lt_of_le hDH hge
      rw [ccog_I_ge a Q hDH hge]
      have key : g * (a - a ^ 2 / (2 * (a * s))) - c * (a * s) = 2 * c * a * s * (s - 1) := by
        rw [hgs]; field_simp; ring
      rw [key]
      have h5 : g * (a - a ^ 2 / (2 * Q)) - c * Q = 2 * c * a * s ^ 2 - c * (s ^ 2 * a ^ 2 / Q + Q) := by
        rw [hgs]; field_simp; ring
      rw [h5]
      have h6 : 2 * s * a ≤ s ^ 2 * a ^ 2 / Q + Q := by
        rw [← sub_nonneg]
        have : s ^ 2 * a ^ 2 / Q + Q - 2 * s * a = (Q - s * a) ^ 2 / Q := by field_simp; ring
        rw [this]; positivity
      nlinarith [mul_le_mul_of_nonneg_left h6 hcQ.le]
  · have := ccog_deriv p hpp (Q0 p) 0 hQ0pos
    refine this.congr_deriv ?_
    rw [hsq, hQ0]
    have : g / (a * s) * (-a - 0 / p.e) + g = -(2 * c * s) + g := by
      rw [hgs]; field_simp; ring
    rw [this]
