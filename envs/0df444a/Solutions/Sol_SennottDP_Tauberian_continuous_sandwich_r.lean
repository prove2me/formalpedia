-- Prove2me | solution 1 for SennottDP.Tauberian.continuous_sandwich_r
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T02:24:41.164898+00:00
-- url     : https://prove2.me/submissions/e4a7891c-b464-49dd-9d10-23a410a1d877

import Mathlib
import Definitions.Def_SennottDP_Tauberian_PowerSeries
import Definitions.Def_SennottDP_Tauberian_KaramataR

open scoped ENNReal NNReal Topology
open Filter

set_option autoImplicit false

namespace SennottSandwichAux

/-- clipped ramp: `min (max x a)⁻¹ (K * max 0 (x - b))`. -/
noncomputable def f (a b K : ℝ) (x : ℝ) : ℝ := min (max x a)⁻¹ (K * max 0 (x - b))

lemma f_cont {a b K : ℝ} (ha : 0 < a) : Continuous (f a b K) := by
  unfold f
  apply Continuous.min
  · exact (continuous_id.max continuous_const).inv₀
      (fun x => (lt_of_lt_of_le ha (le_max_right x a)).ne')
  · exact continuous_const.mul (continuous_const.max (continuous_id.sub continuous_const))

lemma f_nonneg {a b K x : ℝ} (ha : 0 < a) (hK : 0 ≤ K) : 0 ≤ f a b K x := by
  unfold f
  apply le_min
  · exact inv_nonneg.mpr (le_trans ha.le (le_max_right _ _))
  · exact mul_nonneg hK (le_max_left _ _)

lemma f_le_inv {a b K x : ℝ} (hx : a ≤ x) : f a b K x ≤ x⁻¹ := by
  unfold f
  rw [max_eq_left hx]
  exact min_le_left _ _

lemma f_le_ramp {a b K x : ℝ} (hK : 0 ≤ K) (hxb : b ≤ x) : f a b K x ≤ K * (x - b) := by
  unfold f
  rw [max_eq_right (sub_nonneg.mpr hxb)]
  exact min_le_right _ _

lemma f_eq_zero {a b K x : ℝ} (ha : 0 < a) (hx : x ≤ b) : f a b K x = 0 := by
  unfold f
  have : max 0 (x - b) = 0 := max_eq_left (by linarith)
  rw [this, mul_zero]
  exact min_eq_right (inv_nonneg.mpr (le_trans ha.le (le_max_right _ _)))

lemma f_eq_inv {a b K x : ℝ} (hx : a ≤ x) (hxb : b ≤ x) (h : x⁻¹ ≤ K * (x - b)) :
    f a b K x = x⁻¹ := by
  unfold f
  rw [max_eq_left hx, max_eq_right (sub_nonneg.mpr hxb)]
  exact min_eq_left h

lemma exp_neg_one_inv : (Real.exp (-1))⁻¹ = Real.exp 1 := by
  rw [Real.exp_neg, inv_inv]

end SennottSandwichAux

open SennottSandwichAux in
open SennottDP.Tauberian in
theorem solution (ε : ℝ) (hε : 0 < ε) :
    ∃ s sstar : ℝ → ℝ, ContinuousOn s (Set.Icc 0 1) ∧ ContinuousOn sstar (Set.Icc 0 1) ∧
      (∀ x ∈ Set.Ioo (0 : ℝ) 1, sstar x ≤ r x ∧ r x ≤ s x) ∧
      1 - ε ≤ ∫ x in (0 : ℝ)..1, sstar x ∧
      ∫ x in (0 : ℝ)..1, sstar x ≤ ∫ x in (0 : ℝ)..1, s x ∧
      ∫ x in (0 : ℝ)..1, s x ≤ 1 + ε := by
  set a : ℝ := Real.exp (-1) with ha_def
  set b : ℝ := Real.exp (-1 - ε) with hb_def
  set c : ℝ := Real.exp (-1 + min ε 1) with hc_def
  have ha : 0 < a := Real.exp_pos _
  have hb : 0 < b := Real.exp_pos _
  have hc : 0 < c := Real.exp_pos _
  have hm : 0 < min ε 1 := lt_min hε one_pos
  have hba : b < a := Real.exp_lt_exp.mpr (by linarith)
  have hac : a < c := Real.exp_lt_exp.mpr (by linarith)
  have hc1 : c ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [min_le_right ε 1])
  have hb1 : b ≤ 1 := le_trans hba.le (le_trans hac.le hc1)
  have hainv : a⁻¹ = Real.exp 1 := exp_neg_one_inv
  set K₁ : ℝ := Real.exp 1 / (a - b) with hK₁
  set K₂ : ℝ := Real.exp 1 / (c - a) with hK₂
  have hK₁0 : 0 ≤ K₁ := div_nonneg (Real.exp_pos 1).le (by linarith)
  have hK₂0 : 0 ≤ K₂ := div_nonneg (Real.exp_pos 1).le (by linarith)
  have hK₁e : K₁ * (a - b) = Real.exp 1 := div_mul_cancel₀ _ (by linarith)
  have hK₂e : K₂ * (c - a) = Real.exp 1 := div_mul_cancel₀ _ (by linarith)
  -- x⁻¹ ≤ exp 1 for x ≥ a
  have hinv_le : ∀ x : ℝ, a ≤ x → x⁻¹ ≤ Real.exp 1 := by
    intro x hx
    rw [← hainv]
    exact inv_anti₀ ha hx
  let s : ℝ → ℝ := f a b K₁
  let sstar : ℝ → ℝ := f a a K₂
  have s_eq : ∀ x, a ≤ x → s x = x⁻¹ := by
    intro x hx
    apply f_eq_inv hx (le_trans hba.le hx)
    calc x⁻¹ ≤ Real.exp 1 := hinv_le x hx
      _ = K₁ * (a - b) := hK₁e.symm
      _ ≤ K₁ * (x - b) := mul_le_mul_of_nonneg_left (by linarith) hK₁0
  have sstar_eq : ∀ x, c ≤ x → sstar x = x⁻¹ := by
    intro x hx
    apply f_eq_inv (le_trans hac.le hx) (le_trans hac.le hx)
    calc x⁻¹ ≤ Real.exp 1 := hinv_le x (le_trans hac.le hx)
      _ = K₂ * (c - a) := hK₂e.symm
      _ ≤ K₂ * (x - a) := mul_le_mul_of_nonneg_left (by linarith) hK₂0
  have s_le_inv : ∀ x, b ≤ x → s x ≤ x⁻¹ := by
    intro x hx
    by_cases hax : a ≤ x
    · exact f_le_inv hax
    · push_neg at hax
      calc s x ≤ K₁ * (x - b) := f_le_ramp hK₁0 hx
        _ ≤ K₁ * (a - b) := mul_le_mul_of_nonneg_left (by linarith) hK₁0
        _ = a⁻¹ := by rw [hK₁e, hainv]
        _ ≤ x⁻¹ := inv_anti₀ (lt_of_lt_of_le hb hx) hax.le
  have sstar_le_r : ∀ x, sstar x ≤ r x := by
    intro x
    unfold r
    split_ifs with hx
    · exact f_le_inv hx
    · push_neg at hx
      exact (f_eq_zero ha hx.le).le
  have r_le_s : ∀ x, r x ≤ s x := by
    intro x
    unfold r
    split_ifs with hx
    · exact (s_eq x hx).ge
    · exact f_nonneg ha hK₁0
  have sstar_le_s : ∀ x, sstar x ≤ s x := fun x => le_trans (sstar_le_r x) (r_le_s x)
  have hs_cont : Continuous s := f_cont ha
  have hss_cont : Continuous sstar := f_cont ha
  have hinv_int : ∀ u v : ℝ, 0 < u → 0 < v →
      IntervalIntegrable (fun x : ℝ => x⁻¹) MeasureTheory.volume u v := by
    intro u v hu hv
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_inv₀.mono
    intro x hx
    rw [Set.mem_uIcc] at hx
    have : 0 < x := by rcases hx with h | h <;> linarith [h.1]
    exact this.ne'
  refine ⟨s, sstar, hs_cont.continuousOn, hss_cont.continuousOn,
    fun x _ => ⟨sstar_le_r x, r_le_s x⟩, ?_, ?_, ?_⟩
  · have h1 : ∫ x in (0:ℝ)..1, sstar x = (∫ x in (0:ℝ)..c, sstar x) + ∫ x in c..1, sstar x :=
      (intervalIntegral.integral_add_adjacent_intervals (hss_cont.intervalIntegrable _ _)
        (hss_cont.intervalIntegrable _ _)).symm
    have h2 : 0 ≤ ∫ x in (0:ℝ)..c, sstar x :=
      intervalIntegral.integral_nonneg hc.le (fun x _ => f_nonneg ha hK₂0)
    have h3 : ∫ x in c..1, sstar x = ∫ x in c..1, x⁻¹ := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le hc1] at hx
      exact sstar_eq x hx.1
    have h4 : ∫ x in c..1, x⁻¹ = 1 - min ε 1 := by
      rw [integral_inv_of_pos hc one_pos, one_div, Real.log_inv, hc_def, Real.log_exp]
      ring
    rw [h1, h3, h4]
    linarith [min_le_left ε 1]
  · exact intervalIntegral.integral_mono_on zero_le_one (hss_cont.intervalIntegrable _ _)
      (hs_cont.intervalIntegrable _ _) (fun x _ => sstar_le_s x)
  · have h1 : ∫ x in (0:ℝ)..1, s x = (∫ x in (0:ℝ)..b, s x) + ∫ x in b..1, s x :=
      (intervalIntegral.integral_add_adjacent_intervals (hs_cont.intervalIntegrable _ _)
        (hs_cont.intervalIntegrable _ _)).symm
    have h2 : ∫ x in (0:ℝ)..b, s x = 0 := by
      have : ∫ x in (0:ℝ)..b, s x = ∫ x in (0:ℝ)..b, (0:ℝ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [Set.uIcc_of_le hb.le] at hx
        exact f_eq_zero ha hx.2
      rw [this, intervalIntegral.integral_zero]
    have h3 : ∫ x in b..1, s x ≤ ∫ x in b..1, x⁻¹ :=
      intervalIntegral.integral_mono_on hb1 (hs_cont.intervalIntegrable _ _)
        (hinv_int b 1 hb one_pos) (fun x hx => s_le_inv x hx.1)
    have h4 : ∫ x in b..1, x⁻¹ = 1 + ε := by
      rw [integral_inv_of_pos hb one_pos, one_div, Real.log_inv, hb_def, Real.log_exp]
      ring
    rw [h1, h2, zero_add]
    linarith
