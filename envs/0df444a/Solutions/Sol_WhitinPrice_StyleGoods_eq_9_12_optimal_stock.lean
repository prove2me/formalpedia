-- Prove2me | solution 1 for WhitinPrice.StyleGoods.eq_9_12_optimal_stock
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-12T22:32:03.072335+00:00
-- url     : https://prove2.me/submissions/fb0043e2-8b1e-4618-9a46-7fbd73fd4d15

import Mathlib
import Definitions.Def_WhitinPrice_StyleGoods_Model



namespace WhitinPrice.StyleGoods
open MeasureTheory ProbabilityTheory

lemma ws_Ici (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    (cond volume (Set.Icc (0:ℝ) a)).real (Set.Ici x) = (a - x) / a := by
  rw [Measure.real, cond_apply measurableSet_Icc]
  have h1 : Set.Icc (0:ℝ) a ∩ Set.Ici x = Set.Icc x a := by
    ext y; simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Ici]
    constructor
    · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨h3, h2⟩
    · rintro ⟨h2, h3⟩; exact ⟨⟨by linarith, h3⟩, h2⟩
  rw [h1, Real.volume_Icc, Real.volume_Icc, sub_zero]
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofReal ha.le,
    ENNReal.toReal_ofReal (by linarith)]
  field_simp

lemma ws_Ici_ge (a x : ℝ) (ha : 0 < a) (hxa : a ≤ x) :
    (cond volume (Set.Icc (0:ℝ) a)).real (Set.Ici x) = 0 := by
  rw [Measure.real, cond_apply measurableSet_Icc]
  have h1 : volume (Set.Icc (0:ℝ) a ∩ Set.Ici x) = 0 := by
    apply measure_mono_null (t := {a})
    · intro y hy
      simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Ici] at hy
      simp only [Set.mem_singleton_iff]; linarith [hy.1.2, hy.2]
    · exact measure_singleton a
  rw [h1]; simp

lemma ws_prob (a : ℝ) (ha : 0 < a) : IsProbabilityMeasure (cond volume (Set.Icc (0:ℝ) a)) := by
  apply cond_isProbabilityMeasure_of_finite
  · simp [Real.volume_Icc, ha]
  · simp [Real.volume_Icc]

lemma ws_Iio (a x : ℝ) (ha : 0 < a) :
    (cond volume (Set.Icc (0:ℝ) a)).real (Set.Iio x) = 1 - (cond volume (Set.Icc (0:ℝ) a)).real (Set.Ici x) := by
  haveI := ws_prob a ha
  rw [← Set.compl_Ici, probReal_compl_eq_one_sub measurableSet_Ici]

lemma ws_mp_le (k P₀ P t : ℝ) (hk : k < 0) (hP : P < P₀) (ht0 : 0 ≤ t)
    (hta : t ≤ 2 * meanDemand k P₀ P) :
    marginalProfit k P₀ P t = P * ((2 * meanDemand k P₀ P - t) / (2 * meanDemand k P₀ P)) := by
  have ha : 0 < 2 * meanDemand k P₀ P := by unfold meanDemand; nlinarith
  unfold marginalProfit demandLaw
  rw [ws_Ici _ _ ha ht0 hta]

lemma ws_ml_le (k P₀ L P t : ℝ) (hk : k < 0) (hP : P < P₀) (ht0 : 0 ≤ t)
    (hta : t ≤ 2 * meanDemand k P₀ P) :
    marginalLoss k P₀ L P t = L * (t / (2 * meanDemand k P₀ P)) := by
  have ha : 0 < 2 * meanDemand k P₀ P := by unfold meanDemand; nlinarith
  unfold marginalLoss demandLaw
  rw [ws_Iio _ _ ha, ws_Ici _ _ ha ht0 hta]
  generalize 2 * meanDemand k P₀ P = a at ha hta ⊢
  field_simp
  ring

lemma ws_diff_le (k P₀ L P t : ℝ) (hk : k < 0) (hP : P < P₀) (ht0 : 0 ≤ t)
    (hta : t ≤ 2 * meanDemand k P₀ P) :
    marginalProfit k P₀ P t - marginalLoss k P₀ L P t
      = P * (2 * meanDemand k P₀ P - t) / (2 * meanDemand k P₀ P) - L * t / (2 * meanDemand k P₀ P) := by
  rw [ws_mp_le k P₀ P t hk hP ht0 hta, ws_ml_le k P₀ L P t hk hP ht0 hta]
  ring

lemma ws_diff_ge (k P₀ L P t : ℝ) (hk : k < 0) (hP : P < P₀)
    (hta : 2 * meanDemand k P₀ P ≤ t) :
    marginalProfit k P₀ P t - marginalLoss k P₀ L P t = -L := by
  have ha : 0 < 2 * meanDemand k P₀ P := by unfold meanDemand; nlinarith
  unfold marginalProfit marginalLoss demandLaw
  rw [ws_Iio _ _ ha, ws_Ici_ge _ _ ha hta]
  ring

lemma ws_int_lin (P c x : ℝ) : ∫ t in (0:ℝ)..x, (P - c * t) = P * x - c * x ^ 2 / 2 := by
  rw [intervalIntegral.integral_sub (by simp) (by apply Continuous.intervalIntegrable; fun_prop)]
  rw [intervalIntegral.integral_const_mul]
  simp [integral_id]
  ring

lemma ws_E_le (k P₀ L P x : ℝ) (hk : k < 0) (hP : P < P₀) (hx0 : 0 ≤ x)
    (hx : x ≤ 2 * meanDemand k P₀ P) :
    expectedProfit k P₀ L P x = P * x - (P + L) * x ^ 2 / (2 * (2 * meanDemand k P₀ P)) := by
  have ha : 0 < 2 * meanDemand k P₀ P := by unfold meanDemand; nlinarith
  unfold expectedProfit
  rw [intervalIntegral.integral_congr (g := fun t => P - (P + L) / (2 * meanDemand k P₀ P) * t)]
  · rw [ws_int_lin]
    generalize 2 * meanDemand k P₀ P = a at ha hx ⊢
    field_simp
  · intro t ht
    rw [Set.uIcc_of_le hx0] at ht
    beta_reduce
    rw [ws_diff_le k P₀ L P t hk hP ht.1 (ht.2.trans hx)]
    generalize 2 * meanDemand k P₀ P = a at ha hx ⊢
    field_simp
    ring

lemma ws_E_ge (k P₀ L P x : ℝ) (hk : k < 0) (hP : P < P₀) (hP0 : 0 < P)
    (hx : 2 * meanDemand k P₀ P ≤ x) :
    expectedProfit k P₀ L P x
      = 2 * meanDemand k P₀ P * (P - L) / 2 - L * (x - 2 * meanDemand k P₀ P) := by
  have ha : 0 < 2 * meanDemand k P₀ P := by unfold meanDemand; nlinarith
  have hEa := ws_E_le k P₀ L P (2 * meanDemand k P₀ P) hk hP ha.le le_rfl
  have h1 : IntervalIntegrable (fun t => marginalProfit k P₀ P t - marginalLoss k P₀ L P t)
      volume 0 (2 * meanDemand k P₀ P) := by
    have hc : IntervalIntegrable (fun t : ℝ => P - (P + L) / (2 * meanDemand k P₀ P) * t)
        volume 0 (2 * meanDemand k P₀ P) :=
      Continuous.intervalIntegrable (by fun_prop) _ _
    refine hc.congr ?_
    intro t ht
    rw [Set.uIoc_of_le ha.le] at ht
    simp only
    rw [ws_diff_le k P₀ L P t hk hP ht.1.le ht.2]
    generalize 2 * meanDemand k P₀ P = a at ha ⊢
    field_simp
    ring
  have h2 : IntervalIntegrable (fun t => marginalProfit k P₀ P t - marginalLoss k P₀ L P t)
      volume (2 * meanDemand k P₀ P) x := by
    have hc : IntervalIntegrable (fun _ : ℝ => -L) volume (2 * meanDemand k P₀ P) x :=
      Continuous.intervalIntegrable (by fun_prop) _ _
    refine hc.congr ?_
    intro t ht
    rw [Set.uIoc_of_le hx] at ht
    simp only
    rw [ws_diff_ge k P₀ L P t hk hP ht.1.le]
  unfold expectedProfit
  rw [← intervalIntegral.integral_add_adjacent_intervals h1 h2]
  have h3 : ∫ t in (2 * meanDemand k P₀ P)..x,
      (marginalProfit k P₀ P t - marginalLoss k P₀ L P t) = (x - 2 * meanDemand k P₀ P) * (-L) := by
    rw [intervalIntegral.integral_congr (g := fun _ => -L)]
    · simp
    · intro t ht
      rw [Set.uIcc_of_le hx] at ht
      exact ws_diff_ge k P₀ L P t hk hP ht.1
  rw [h3]
  unfold expectedProfit at hEa
  rw [hEa]
  generalize 2 * meanDemand k P₀ P = a at ha ⊢
  field_simp
  ring

lemma ws_pos (k P₀ P : ℝ) (hk : k < 0) (hP : P < P₀) : 0 < 2 * meanDemand k P₀ P := by
  unfold meanDemand; nlinarith

lemma ws_xM (k P₀ L P : ℝ) (hP : 0 < P) (hL : 0 < L) :
    optimalStock k P₀ L P = P * (2 * meanDemand k P₀ P) / (P + L) := by
  unfold optimalStock meanDemand
  have : P + L ≠ 0 := by positivity
  field_simp
  ring

theorem eq11_core (k P₀ L P x : ℝ) (hk : k < 0) (hL : 0 < L) (hP : 0 < P)
    (hPP₀ : P < P₀) (hx₀ : 0 ≤ x) (hx : x ≤ 2 * meanDemand k P₀ P) :
    marginalProfit k P₀ P x = P / (2 * k * (P₀ - P)) * x + P ∧
      marginalLoss k P₀ L P x = -L / (2 * k * (P₀ - P)) * x := by
  rw [ws_mp_le k P₀ P x hk hPP₀ hx₀ hx, ws_ml_le k P₀ L P x hk hPP₀ hx₀ hx]
  have h : k * (P₀ - P) ≠ 0 := mul_ne_zero hk.ne (by linarith)
  have h2 : 2 * meanDemand k P₀ P = -(2 * k * (P₀ - P)) := by unfold meanDemand; ring
  rw [h2]
  have h3 : 2 * k * (P₀ - P) ≠ 0 := by
    have : 2 * k * (P₀ - P) = 2 * (k * (P₀ - P)) := by ring
    rw [this]; exact mul_ne_zero two_ne_zero h
  generalize 2 * k * (P₀ - P) = c at h3 ⊢
  constructor
  · field_simp
    ring
  · field_simp

theorem eq13_core (k P₀ L P x : ℝ) (hk : k < 0) (hL : 0 < L) (hP : 0 < P)
    (hPP₀ : P < P₀) (hx₀ : 0 ≤ x) (hx : x ≤ 2 * meanDemand k P₀ P) :
    expectedProfit k P₀ L P x = (P + L) / (4 * k * (P₀ - P)) * x ^ 2 + P * x := by
  rw [ws_E_le k P₀ L P x hk hPP₀ hx₀ hx]
  have h : k * (P₀ - P) ≠ 0 := mul_ne_zero hk.ne (by linarith)
  have h2 : 2 * meanDemand k P₀ P = -(2 * k * (P₀ - P)) := by unfold meanDemand; ring
  rw [h2]
  have h3 : 2 * k * (P₀ - P) ≠ 0 := by
    have : 2 * k * (P₀ - P) = 2 * (k * (P₀ - P)) := by ring
    rw [this]; exact mul_ne_zero two_ne_zero h
  have h4 : 4 * k * (P₀ - P) ≠ 0 := by
    have : 4 * k * (P₀ - P) = 4 * (k * (P₀ - P)) := by ring
    rw [this]; exact mul_ne_zero (by norm_num) h
  field_simp
  ring

lemma ws_gap (k P₀ L P x : ℝ) (hk : k < 0) (hL : 0 < L) (hP : 0 < P)
    (hPP₀ : P < P₀) (hx0 : 0 ≤ x) :
    expectedProfit k P₀ L P x ≤ expectedProfit k P₀ L P (optimalStock k P₀ L P) ∧
    (expectedProfit k P₀ L P x = expectedProfit k P₀ L P (optimalStock k P₀ L P) →
      x = optimalStock k P₀ L P) := by
  have ha := ws_pos k P₀ P hk hPP₀
  have hxM := ws_xM k P₀ L P hP hL
  have hPL : 0 < P + L := by linarith
  have hxM0 : 0 < optimalStock k P₀ L P := by rw [hxM]; positivity
  have hxMa : optimalStock k P₀ L P < 2 * meanDemand k P₀ P := by
    rw [hxM, div_lt_iff₀ hPL]; nlinarith
  have hEM := ws_E_le k P₀ L P _ hk hPP₀ hxM0.le hxMa.le
  rcases le_or_gt x (2 * meanDemand k P₀ P) with h | h
  · rw [ws_E_le k P₀ L P x hk hPP₀ hx0 h, hEM]
    have key : (P * optimalStock k P₀ L P - (P + L) * optimalStock k P₀ L P ^ 2 / (2 * (2 * meanDemand k P₀ P)))
        - (P * x - (P + L) * x ^ 2 / (2 * (2 * meanDemand k P₀ P)))
        = (P + L) * (x - optimalStock k P₀ L P) ^ 2 / (2 * (2 * meanDemand k P₀ P)) := by
      rw [hxM]
      generalize 2 * meanDemand k P₀ P = a at ha ⊢
      field_simp
      ring
    have hnn : 0 ≤ (P + L) * (x - optimalStock k P₀ L P) ^ 2 / (2 * (2 * meanDemand k P₀ P)) := by
      positivity
    refine ⟨by linarith, fun heq => ?_⟩
    have h0 : (P + L) * (x - optimalStock k P₀ L P) ^ 2 / (2 * (2 * meanDemand k P₀ P)) = 0 := by
      linarith
    rw [div_eq_zero_iff] at h0
    rcases h0 with h0 | h0
    · rcases mul_eq_zero.mp h0 with h1 | h1
      · linarith
      · have := pow_eq_zero_iff (two_ne_zero) |>.mp h1; linarith
    · linarith
  · rw [ws_E_ge k P₀ L P x hk hPP₀ hP h.le, hEM]
    have key : (P * optimalStock k P₀ L P - (P + L) * optimalStock k P₀ L P ^ 2 / (2 * (2 * meanDemand k P₀ P)))
        - (2 * meanDemand k P₀ P * (P - L) / 2 - L * (x - 2 * meanDemand k P₀ P))
        = (P + L) * (2 * meanDemand k P₀ P - optimalStock k P₀ L P) ^ 2 / (2 * (2 * meanDemand k P₀ P))
          + L * (x - 2 * meanDemand k P₀ P) := by
      rw [hxM]
      generalize 2 * meanDemand k P₀ P = a at ha ⊢
      field_simp
      ring
    have hp1 : 0 ≤ (P + L) * (2 * meanDemand k P₀ P - optimalStock k P₀ L P) ^ 2 / (2 * (2 * meanDemand k P₀ P)) := by
      positivity
    have hp2 : 0 < L * (x - 2 * meanDemand k P₀ P) := mul_pos hL (by linarith)
    constructor
    · linarith
    · intro heq; linarith

theorem eq912_core (k P₀ L P : ℝ) (hk : k < 0) (hL : 0 < L) (hP : 0 < P)
    (hPP₀ : P < P₀) :
    0 < optimalStock k P₀ L P ∧ optimalStock k P₀ L P < 2 * meanDemand k P₀ P ∧
      (∀ x : ℝ, 0 ≤ x →
        (marginalProfit k P₀ P x - marginalLoss k P₀ L P x = 0 ↔ x = optimalStock k P₀ L P)) ∧
      (∀ x : ℝ, 0 ≤ x → expectedProfit k P₀ L P x ≤ expectedProfit k P₀ L P (optimalStock k P₀ L P)) ∧
      (∀ x : ℝ, 0 ≤ x →
        expectedProfit k P₀ L P x = expectedProfit k P₀ L P (optimalStock k P₀ L P) →
          x = optimalStock k P₀ L P) := by
  have ha := ws_pos k P₀ P hk hPP₀
  have hxM := ws_xM k P₀ L P hP hL
  have hPL : 0 < P + L := by linarith
  have hxM0 : 0 < optimalStock k P₀ L P := by rw [hxM]; positivity
  have hxMa : optimalStock k P₀ L P < 2 * meanDemand k P₀ P := by
    rw [hxM, div_lt_iff₀ hPL]; nlinarith
  refine ⟨hxM0, hxMa, ?_, fun x hx => (ws_gap k P₀ L P x hk hL hP hPP₀ hx).1,
    fun x hx => (ws_gap k P₀ L P x hk hL hP hPP₀ hx).2⟩
  intro x hx
  rcases le_or_gt x (2 * meanDemand k P₀ P) with h | h
  · rw [ws_diff_le k P₀ L P x hk hPP₀ hx h, hxM]
    generalize 2 * meanDemand k P₀ P = a at ha h ⊢
    constructor
    · intro h0
      field_simp at h0 ⊢
      linarith
    · intro h0
      rw [h0]
      field_simp
      ring
  · rw [ws_diff_ge k P₀ L P x hk hPP₀ h.le]
    constructor
    · intro h0; linarith
    · intro h0; linarith

theorem eq14_core (k P₀ L P : ℝ) (hk : k < 0) (hL : 0 < L) (hP : 0 < P)
    (hPP₀ : P < P₀) :
    expectedProfit k P₀ L P (optimalStock k P₀ L P) = -(k * P ^ 2 * (P₀ - P)) / (P + L) := by
  have ha := ws_pos k P₀ P hk hPP₀
  have hxM := ws_xM k P₀ L P hP hL
  have hPL : 0 < P + L := by linarith
  have hxM0 : 0 < optimalStock k P₀ L P := by rw [hxM]; positivity
  have hxMa : optimalStock k P₀ L P < 2 * meanDemand k P₀ P := by
    rw [hxM, div_lt_iff₀ hPL]; nlinarith
  rw [ws_E_le k P₀ L P _ hk hPP₀ hxM0.le hxMa.le, hxM]
  have h2 : 2 * meanDemand k P₀ P = -(2 * k * (P₀ - P)) := by unfold meanDemand; ring
  have hne : (2 * meanDemand k P₀ P) ≠ 0 := ha.ne'
  have hPL' : P + L ≠ 0 := hPL.ne'
  field_simp
  unfold meanDemand
  ring

end WhitinPrice.StyleGoods

open WhitinPrice.StyleGoods


theorem solution (k P₀ L P : ℝ) (hk : k < 0) (hL : 0 < L) (hP : 0 < P)
    (hPP₀ : P < P₀) :
    0 < optimalStock k P₀ L P ∧ optimalStock k P₀ L P < 2 * meanDemand k P₀ P ∧
      (∀ x : ℝ, 0 ≤ x →
        (marginalProfit k P₀ P x - marginalLoss k P₀ L P x = 0 ↔ x = optimalStock k P₀ L P)) ∧
      (∀ x : ℝ, 0 ≤ x → expectedProfit k P₀ L P x ≤ expectedProfit k P₀ L P (optimalStock k P₀ L P)) ∧
      (∀ x : ℝ, 0 ≤ x →
        expectedProfit k P₀ L P x = expectedProfit k P₀ L P (optimalStock k P₀ L P) →
          x = optimalStock k P₀ L P) := by
  exact eq912_core k P₀ L P hk hL hP hPP₀
