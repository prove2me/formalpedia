-- Prove2me | solution 1 for RogersSatchell.Correction.overshoot_max_moments
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-26T04:52:17.986818+00:00
-- url     : https://prove2.me/submissions/3b264ec6-02df-4f53-b747-28fde7d3f977

import Mathlib
import Definitions.Def_RogersSatchell_Correction_OvershootLaw
import Definitions.Def_RogersSatchell_Correction_Constants

set_option autoImplicit false

open MeasureTheory Set Real Filter Topology

namespace RSOvershoot

lemma gauss0 {b : ℝ} (hb : 0 < b) :
    ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (exp (-b * t ^ 2)) = ENNReal.ofReal (√(π / b) / 2) := by
  rw [← integral_gaussian_Ioi b, ofReal_integral_eq_lintegral_ofReal]
  · exact (integrable_exp_neg_mul_sq hb).integrableOn
  · exact Eventually.of_forall (fun t => (exp_pos _).le)

lemma gauss1_real {b : ℝ} (hb : 0 < b) :
    ∫ t in Ioi (0:ℝ), 2 * (t * exp (-b * t ^ 2)) = 1 / b := by
  have hderiv : ∀ x ∈ Ici (0:ℝ), HasDerivAt (fun t => -exp (-b * t ^ 2) / b)
      (2 * (x * exp (-b * x ^ 2))) x := by
    intro x _
    have h1 : HasDerivAt (fun t => -b * t ^ 2) (-b * (2 * x)) x := by
      simpa using ((hasDerivAt_pow 2 x).const_mul (-b))
    have h2 := (h1.exp.neg).div_const b
    refine h2.congr_deriv ?_
    have hb0 := hb.ne'
    field_simp
  have hint : IntegrableOn (fun x => 2 * (x * exp (-b * x ^ 2))) (Ioi 0) :=
    ((integrable_mul_exp_neg_mul_sq hb).const_mul 2).integrableOn
  have hlim : Tendsto (fun t => -exp (-b * t ^ 2) / b) atTop (𝓝 0) := by
    have h0 : Tendsto (fun t : ℝ => -b * t ^ 2) atTop atBot := by
      have : Tendsto (fun t : ℝ => b * t ^ 2) atTop atTop :=
        (tendsto_pow_atTop two_ne_zero).const_mul_atTop hb
      refine (tendsto_neg_atTop_atBot.comp this).congr (fun t => ?_)
      simp [neg_mul]
    have h3 := ((tendsto_exp_atBot.comp h0).neg).div_const b
    simpa using h3
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint hlim]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, Real.exp_zero]
  ring

lemma gauss1 {b : ℝ} (hb : 0 < b) :
    ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (2 * (t * exp (-b * t ^ 2))) = ENNReal.ofReal (1 / b) := by
  rw [← gauss1_real hb, ofReal_integral_eq_lintegral_ofReal]
  · exact ((integrable_mul_exp_neg_mul_sq hb).const_mul 2).integrableOn
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have : (0:ℝ) < t := ht
    positivity

/-- set-lintegral over `Ioc 0 1` of a continuous nonnegative function. -/
lemma lint_Ioc {f : ℝ → ℝ} (hf : ContinuousOn f (Icc 0 1)) (hnn : ∀ v ∈ Ioc (0:ℝ) 1, 0 ≤ f v) :
    ∫⁻ v in Ioc (0:ℝ) 1, ENNReal.ofReal (f v) = ENNReal.ofReal (∫ v in (0:ℝ)..1, f v) := by
  rw [intervalIntegral.integral_of_le zero_le_one, ofReal_integral_eq_lintegral_ofReal
    (hf.integrableOn_Icc.mono_set Ioc_subset_Icc_self)]
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
  exact hnn v hv

lemma I3 {v : ℝ} (hv : 0 < v) :
    ∫ w in (0:ℝ)..1, w / √(v ^ 2 + w ^ 2) = √(v ^ 2 + 1) - v := by
  have hpos : ∀ w : ℝ, 0 < v ^ 2 + w ^ 2 := fun w => by positivity
  have hd : ∀ x ∈ uIcc (0:ℝ) 1, HasDerivAt (fun w => √(v ^ 2 + w ^ 2))
      (x / √(v ^ 2 + x ^ 2)) x := by
    intro x _
    have h1 : HasDerivAt (fun w => v ^ 2 + w ^ 2) (2 * x) x := by
      simpa using ((hasDerivAt_pow 2 x).const_add (v ^ 2))
    refine (h1.sqrt (hpos x).ne').congr_deriv ?_
    exact mul_div_mul_left x (√(v ^ 2 + x ^ 2)) (two_ne_zero : (2:ℝ) ≠ 0)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd]
  · simp [Real.sqrt_sq hv.le]
  · apply Continuous.intervalIntegrable
    exact continuous_id.div (by fun_prop) (fun w => (Real.sqrt_pos.2 (hpos w)).ne')

lemma I4 : ∫ v in (0:ℝ)..1, v * (√(v ^ 2 + 1) - v) = (2 * √2 - 2) / 3 := by
  have hpos : ∀ w : ℝ, 0 < w ^ 2 + 1 := fun w => by positivity
  have hd : ∀ x ∈ uIcc (0:ℝ) 1, HasDerivAt (fun w => ((w ^ 2 + 1) * √(w ^ 2 + 1) - w ^ 3) / 3)
      (x * (√(x ^ 2 + 1) - x)) x := by
    intro x _
    have h1 : HasDerivAt (fun w => w ^ 2 + 1) (2 * x) x := by
      simpa using ((hasDerivAt_pow 2 x).add_const 1)
    have h2 := ((h1.mul (h1.sqrt (hpos x).ne')).sub (hasDerivAt_pow 3 x)).div_const 3
    refine h2.congr_deriv ?_
    have hs : √(x ^ 2 + 1) ≠ 0 := (Real.sqrt_pos.2 (hpos x)).ne'
    have hsq : √(x ^ 2 + 1) ^ 2 = x ^ 2 + 1 := Real.sq_sqrt (hpos x).le
    simp only [Nat.cast_ofNat]
    set s := √(x ^ 2 + 1)
    rw [← hsq]
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd]
  · have : √((1:ℝ) ^ 2 + 1) = √2 := by norm_num
    simp only [this]
    norm_num
    ring
  · apply Continuous.intervalIntegrable
    fun_prop

lemma I5 {v : ℝ} (hv : 0 < v) :
    ∫ w in (0:ℝ)..1, v ^ 2 * w ^ 2 / (v ^ 2 + w ^ 2) = v ^ 2 * (1 - v * arctan (1 / v)) := by
  have hpos : ∀ w : ℝ, 0 < v ^ 2 + w ^ 2 := fun w => by positivity
  have hd : ∀ x ∈ uIcc (0:ℝ) 1, HasDerivAt (fun w => v ^ 2 * (w - v * arctan (w / v)))
      (v ^ 2 * x ^ 2 / (v ^ 2 + x ^ 2)) x := by
    intro x _
    have h1 : HasDerivAt (fun w => w / v) (1 / v) x := by
      simpa using (hasDerivAt_id x).div_const v
    have h2 := ((hasDerivAt_id x).sub (h1.arctan.const_mul v)).const_mul (v ^ 2)
    refine h2.congr_deriv ?_
    have : v ^ 2 + x ^ 2 ≠ 0 := (hpos x).ne'
    have hv0 := hv.ne'
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd]
  · simp
  · apply Continuous.intervalIntegrable
    exact (by fun_prop : Continuous fun w : ℝ => v ^ 2 * w ^ 2).div (by fun_prop)
      (fun w => (hpos w).ne')

lemma I6 : ∫ v in (0:ℝ)..1, (v ^ 2 - v ^ 3 * (π / 2 - arctan v)) = 1 / 2 - π / 8 := by
  have hd : ∀ x ∈ uIcc (0:ℝ) 1, HasDerivAt
      (fun v => v ^ 3 / 3 - π * v ^ 4 / 8 + v ^ 4 / 4 * arctan v - (v ^ 3 / 3 - v + arctan v) / 4)
      (x ^ 2 - x ^ 3 * (π / 2 - arctan x)) x := by
    intro x _
    have ha := Real.hasDerivAt_arctan x
    have h := ((((hasDerivAt_pow 3 x).div_const 3).sub (((hasDerivAt_pow 4 x).const_mul π).div_const 8)).add
      (((hasDerivAt_pow 4 x).div_const 4).mul ha)).sub
      ((((hasDerivAt_pow 3 x).div_const 3).sub (hasDerivAt_id x)).add ha |>.div_const 4)
    refine h.congr_deriv ?_
    have : (1 + x ^ 2) ≠ 0 := by positivity
    simp only [Nat.cast_ofNat]
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd]
  · simp [Real.arctan_one]
    ring
  · apply Continuous.intervalIntegrable
    fun_prop


open scoped ENNReal

noncomputable def ell (c t : ℝ) : ℝ≥0∞ :=
  ∫⁻ v in Ioc (0:ℝ) 1, ENNReal.ofReal (exp (-(c / v ^ 2) * t ^ 2))

lemma meas_phi (c : ℝ) :
    Measurable (fun p : ℝ × ℝ => ENNReal.ofReal (exp (-(c / p.2 ^ 2) * p.1 ^ 2))) := by
  fun_prop

lemma ell_meas (c : ℝ) : Measurable (ell c) := (meas_phi c).lintegral_prod_right'

lemma ell_le_one {c : ℝ} (hc : 0 ≤ c) (t : ℝ) : ell c t ≤ 1 := by
  calc ell c t ≤ ∫⁻ v in Ioc (0:ℝ) 1, 1 := lintegral_mono (fun v => ?_)
    _ = 1 := by simp
  rw [ENNReal.ofReal_le_one, Real.exp_le_one_iff]
  have := mul_nonneg (div_nonneg hc (sq_nonneg v)) (sq_nonneg t)
  linarith

lemma ell_zero (c : ℝ) : ell c 0 = 1 := by
  simp [ell]

lemma swap3 (H : ℝ → ℝ → ℝ → ℝ≥0∞)
    (hH : Measurable (fun p : (ℝ × ℝ) × ℝ => H p.1.1 p.1.2 p.2)) (μ ν : Measure ℝ)
    [SFinite μ] [SFinite ν] :
    ∫⁻ t, ∫⁻ v, ∫⁻ w, H t v w ∂ν ∂ν ∂μ = ∫⁻ v, ∫⁻ w, ∫⁻ t, H t v w ∂μ ∂ν ∂ν := by
  rw [lintegral_lintegral_swap (f := fun t v => ∫⁻ w, H t v w ∂ν)
    hH.lintegral_prod_right'.aemeasurable]
  congr 1; funext v
  apply lintegral_lintegral_swap
  have : Measurable (fun p : ℝ × ℝ => H p.1 v p.2) :=
    hH.comp ((measurable_fst.prodMk measurable_const).prodMk measurable_snd)
  exact this.aemeasurable

lemma M1 {c : ℝ} (hc : 0 < c) :
    ∫⁻ t in Ioi (0:ℝ), ell c t = ENNReal.ofReal (√(π / c) / 2 * (1 / 2)) := by
  unfold ell
  rw [lintegral_lintegral_swap ((meas_phi c).aemeasurable)]
  have h : ∀ v ∈ Ioc (0:ℝ) 1, ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (exp (-(c / v ^ 2) * t ^ 2))
      = ENNReal.ofReal (√(π / c) / 2 * v) := by
    intro v hv
    have hv0 : v ≠ 0 := hv.1.ne'
    have hc0 : c ≠ 0 := hc.ne'
    rw [gauss0 (div_pos hc (pow_pos hv.1 2))]
    congr 1
    rw [show π / (c / v ^ 2) = π / c * v ^ 2 by field_simp, Real.sqrt_mul (by positivity),
      Real.sqrt_sq hv.1.le]
    ring
  rw [setLIntegral_congr_fun measurableSet_Ioc h,
    lint_Ioc (by fun_prop) (fun v hv => by have := hv.1; positivity)]
  congr 1
  rw [intervalIntegral.integral_const_mul, integral_id]
  norm_num

lemma M2 {c : ℝ} (hc : 0 < c) :
    ∫⁻ t in Ioi (0:ℝ), ell c t * ENNReal.ofReal (2 * t) = ENNReal.ofReal (1 / c * (1 / 3)) := by
  have e1 : ∀ t, ell c t * ENNReal.ofReal (2 * t) =
      ∫⁻ v in Ioc (0:ℝ) 1, ENNReal.ofReal (2 * (t * exp (-(c / v ^ 2) * t ^ 2))) := by
    intro t
    unfold ell
    rw [← lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
    congr 1; funext v
    rw [← ENNReal.ofReal_mul (exp_pos _).le]
    congr 1; ring
  simp_rw [e1]
  rw [lintegral_lintegral_swap (by fun_prop)]
  have h : ∀ v ∈ Ioc (0:ℝ) 1,
      ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (2 * (t * exp (-(c / v ^ 2) * t ^ 2)))
      = ENNReal.ofReal (1 / c * v ^ 2) := by
    intro v hv
    have hv0 : v ≠ 0 := hv.1.ne'
    have hc0 : c ≠ 0 := hc.ne'
    rw [gauss1 (div_pos hc (pow_pos hv.1 2))]
    congr 1
    field_simp
  rw [setLIntegral_congr_fun measurableSet_Ioc h,
    lint_Ioc (by fun_prop) (fun v hv => by positivity)]
  congr 1
  rw [intervalIntegral.integral_const_mul, integral_pow]
  norm_num

lemma ell_sq {c : ℝ} (hc : 0 ≤ c) (t : ℝ) : ell c t * ell c t =
    ∫⁻ v in Ioc (0:ℝ) 1, ∫⁻ w in Ioc (0:ℝ) 1,
      ENNReal.ofReal (exp (-(c / v ^ 2 + c / w ^ 2) * t ^ 2)) := by
  have hfin : ell c t ≠ ∞ := (lt_of_le_of_lt (ell_le_one hc t) ENNReal.one_lt_top).ne
  rw [show ell c t * ell c t = (∫⁻ v in Ioc (0:ℝ) 1, ENNReal.ofReal (exp (-(c / v ^ 2) * t ^ 2)))
      * ell c t from rfl, ← lintegral_mul_const' _ _ hfin]
  congr 1; funext v
  rw [ell, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  congr 1; funext w
  rw [← ENNReal.ofReal_mul (exp_pos _).le, ← Real.exp_add]
  congr 2; ring

lemma sqrt_id3 {c v w : ℝ} (hc : 0 < c) (hv : 0 < v) (hw : 0 < w) :
    √(π / (c / v ^ 2 + c / w ^ 2)) / 2 = √(π / c) / 2 * (v * (w / √(v ^ 2 + w ^ 2))) := by
  have hp : 0 < v ^ 2 + w ^ 2 := by positivity
  have hs : 0 < √(v ^ 2 + w ^ 2) := Real.sqrt_pos.2 hp
  have e : π / (c / v ^ 2 + c / w ^ 2) = π / c * (v * (w / √(v ^ 2 + w ^ 2))) ^ 2 := by
    rw [mul_pow, div_pow, Real.sq_sqrt hp.le]
    have := hv.ne'; have := hw.ne'; have := hc.ne'; have := hp.ne'
    field_simp
    ring
  rw [e, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  ring

lemma M3 {c : ℝ} (hc : 0 < c) :
    ∫⁻ t in Ioi (0:ℝ), ell c t * ell c t =
      ENNReal.ofReal (√(π / c) / 2 * ((2 * √2 - 2) / 3)) := by
  simp_rw [ell_sq hc.le]
  rw [swap3 (fun t v w => ENNReal.ofReal (exp (-(c / v ^ 2 + c / w ^ 2) * t ^ 2)))
    (by fun_prop)]
  have h : ∀ v ∈ Ioc (0:ℝ) 1, ∫⁻ w in Ioc (0:ℝ) 1, ∫⁻ t in Ioi (0:ℝ),
      ENNReal.ofReal (exp (-(c / v ^ 2 + c / w ^ 2) * t ^ 2))
      = ENNReal.ofReal (√(π / c) / 2 * (v * (√(v ^ 2 + 1) - v))) := by
    intro v hv
    have hv0 := hv.1
    have hw : ∀ w ∈ Ioc (0:ℝ) 1, ∫⁻ t in Ioi (0:ℝ),
        ENNReal.ofReal (exp (-(c / v ^ 2 + c / w ^ 2) * t ^ 2))
        = ENNReal.ofReal (√(π / c) / 2 * (v * (w / √(v ^ 2 + w ^ 2)))) := by
      intro w hw
      rw [gauss0 (add_pos (div_pos hc (pow_pos hv.1 2)) (div_pos hc (pow_pos hw.1 2))),
        sqrt_id3 hc hv.1 hw.1]
    have hcont : ContinuousOn (fun w => √(π / c) / 2 * (v * (w / √(v ^ 2 + w ^ 2)))) (Icc 0 1) := by
      apply Continuous.continuousOn
      refine continuous_const.mul (continuous_const.mul (continuous_id.div (by fun_prop) ?_))
      intro w; exact (Real.sqrt_pos.2 (by positivity)).ne'
    rw [setLIntegral_congr_fun measurableSet_Ioc hw,
      lint_Ioc hcont (fun w hw => by have := hw.1; positivity)]
    congr 1
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, I3 hv.1]
  have hnn : ∀ v ∈ Ioc (0:ℝ) 1, 0 ≤ √(π / c) / 2 * (v * (√(v ^ 2 + 1) - v)) := by
    intro v hv
    have : v ≤ √(v ^ 2 + 1) := by
      calc v = √(v ^ 2) := (Real.sqrt_sq hv.1.le).symm
        _ ≤ √(v ^ 2 + 1) := Real.sqrt_le_sqrt (by linarith)
    have := hv.1
    have : 0 ≤ √(v ^ 2 + 1) - v := by linarith
    positivity
  rw [setLIntegral_congr_fun measurableSet_Ioc h, lint_Ioc (by fun_prop) hnn]
  congr 1
  rw [intervalIntegral.integral_const_mul, I4]

lemma ell_sq2 {c : ℝ} (hc : 0 ≤ c) (t : ℝ) : ell c t * ell c t * ENNReal.ofReal (2 * t) =
    ∫⁻ v in Ioc (0:ℝ) 1, ∫⁻ w in Ioc (0:ℝ) 1,
      ENNReal.ofReal (2 * (t * exp (-(c / v ^ 2 + c / w ^ 2) * t ^ 2))) := by
  rw [ell_sq hc, ← lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
  congr 1; funext v
  rw [← lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
  congr 1; funext w
  rw [← ENNReal.ofReal_mul (exp_pos _).le]
  congr 1; ring

lemma M4 {c : ℝ} (hc : 0 < c) :
    ∫⁻ t in Ioi (0:ℝ), ell c t * ell c t * ENNReal.ofReal (2 * t) =
      ENNReal.ofReal (1 / c * (1 / 2 - π / 8)) := by
  simp_rw [ell_sq2 hc.le]
  rw [swap3 (fun t v w => ENNReal.ofReal (2 * (t * exp (-(c / v ^ 2 + c / w ^ 2) * t ^ 2))))
    (by fun_prop)]
  have h : ∀ v ∈ Ioc (0:ℝ) 1, ∫⁻ w in Ioc (0:ℝ) 1, ∫⁻ t in Ioi (0:ℝ),
      ENNReal.ofReal (2 * (t * exp (-(c / v ^ 2 + c / w ^ 2) * t ^ 2)))
      = ENNReal.ofReal (1 / c * (v ^ 2 - v ^ 3 * (π / 2 - arctan v))) := by
    intro v hv
    have hv0 := hv.1
    have hw : ∀ w ∈ Ioc (0:ℝ) 1, ∫⁻ t in Ioi (0:ℝ),
        ENNReal.ofReal (2 * (t * exp (-(c / v ^ 2 + c / w ^ 2) * t ^ 2)))
        = ENNReal.ofReal (1 / c * (v ^ 2 * w ^ 2 / (v ^ 2 + w ^ 2))) := by
      intro w hw
      rw [gauss1 (add_pos (div_pos hc (pow_pos hv.1 2)) (div_pos hc (pow_pos hw.1 2)))]
      congr 1
      have := hv.1.ne'; have := hw.1.ne'; have := hc.ne'
      have : v ^ 2 + w ^ 2 ≠ 0 := by positivity
      field_simp
      ring
    have hcont : ContinuousOn (fun w => 1 / c * (v ^ 2 * w ^ 2 / (v ^ 2 + w ^ 2))) (Icc 0 1) := by
      apply Continuous.continuousOn
      refine continuous_const.mul ((by fun_prop : Continuous fun w : ℝ => v ^ 2 * w ^ 2).div
        (by fun_prop) ?_)
      intro w; positivity
    rw [setLIntegral_congr_fun measurableSet_Ioc hw,
      lint_Ioc hcont (fun w hw => by positivity)]
    congr 1
    rw [intervalIntegral.integral_const_mul, I5 hv.1, one_div v, Real.arctan_inv_of_pos hv.1]
    ring
  have hnn : ∀ v ∈ Ioc (0:ℝ) 1, 0 ≤ 1 / c * (v ^ 2 - v ^ 3 * (π / 2 - arctan v)) := by
    intro v hv
    have h1 : 0 ≤ ∫ w in (0:ℝ)..1, v ^ 2 * w ^ 2 / (v ^ 2 + w ^ 2) :=
      intervalIntegral.integral_nonneg zero_le_one (fun w _ => by positivity)
    rw [I5 hv.1, one_div v, Real.arctan_inv_of_pos hv.1] at h1
    have : 0 ≤ v ^ 2 - v ^ 3 * (π / 2 - arctan v) := by linarith
    positivity
  rw [setLIntegral_congr_fun measurableSet_Ioc h, lint_Ioc (by fun_prop) hnn]
  congr 1
  rw [intervalIntegral.integral_const_mul, I6]


lemma pack {E : ℝ → ℝ≥0∞} (hE : Measurable E) (hfin : ∀ t, E t ≠ ∞) {V : ℝ} (hV : 0 ≤ V)
    (h : ∫⁻ t in Ioi (0:ℝ), E t = ENNReal.ofReal V) :
    IntegrableOn (fun t => (E t).toReal) (Ioi 0) ∧ ∫ t in Ioi (0:ℝ), (E t).toReal = V := by
  refine ⟨integrable_toReal_of_lintegral_ne_top hE.aemeasurable
    (by rw [h]; exact ENNReal.ofReal_ne_top), ?_⟩
  rw [integral_toReal hE.aemeasurable (Eventually.of_forall (fun t => (hfin t).lt_top)), h,
    ENNReal.toReal_ofReal hV]

lemma surv_eq {σ h : ℝ} (hσ : 0 < σ) (hh : 0 < h) (t : ℝ) :
    RogersSatchell.Correction.overshootSurvival σ h t = (ell (2 / (σ ^ 2 * h)) t).toReal := by
  unfold RogersSatchell.Correction.overshootSurvival
  have hmeas : Measurable (fun u : ℝ => exp (-2 * t ^ 2 / (u * σ ^ 2)) *
      (4 * u * h) ^ (-(1 / 2 : ℝ))) := by fun_prop
  rw [integral_eq_lintegral_of_nonneg_ae _ hmeas.aestronglyMeasurable]
  · congr 1
    have himg : (fun v : ℝ => h * v ^ 2) '' Ioc 0 1 = Ioc 0 h := by
      ext u; constructor
      · rintro ⟨v, hv, rfl⟩
        have := hv.1
        refine ⟨by positivity, ?_⟩
        have : v ^ 2 ≤ 1 := by nlinarith [hv.1, hv.2]
        nlinarith
      · rintro ⟨hu0, hu1⟩
        refine ⟨√(u / h), ⟨Real.sqrt_pos.2 (div_pos hu0 hh), ?_⟩, ?_⟩
        · calc √(u / h) ≤ √1 := Real.sqrt_le_sqrt ((div_le_one hh).2 hu1)
            _ = 1 := Real.sqrt_one
        · simp only
          rw [Real.sq_sqrt (div_pos hu0 hh).le]
          field_simp
    have hderiv : ∀ v ∈ Ioc (0:ℝ) 1, HasDerivWithinAt (fun v : ℝ => h * v ^ 2) (2 * h * v)
        (Ioc 0 1) v := by
      intro v _
      refine (((hasDerivAt_pow 2 v).const_mul h).congr_deriv ?_).hasDerivWithinAt
      simp only [Nat.cast_ofNat]
      ring
    have hinj : InjOn (fun v : ℝ => h * v ^ 2) (Ioc 0 1) := by
      intro x hx y hy hxy
      have h2 : x ^ 2 = y ^ 2 := mul_left_cancel₀ hh.ne' hxy
      exact (pow_left_inj₀ hx.1.le hy.1.le two_ne_zero).1 h2
    rw [← himg, lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioc hderiv hinj]
    unfold ell
    apply setLIntegral_congr_fun measurableSet_Ioc
    intro v hv
    have hv0 := hv.1
    simp only
    rw [← ENNReal.ofReal_mul (abs_nonneg _)]
    congr 1
    rw [abs_of_pos (by positivity)]
    have e1 : (4 * (h * v ^ 2) * h) ^ (-(1 / 2 : ℝ)) = (2 * h * v)⁻¹ := by
      rw [Real.rpow_neg (by positivity), show 4 * (h * v ^ 2) * h = (2 * h * v) ^ 2 by ring,
        ← Real.sqrt_eq_rpow, Real.sqrt_sq (by positivity)]
    rw [e1]
    have hne : 2 * h * v ≠ 0 := by positivity
    have e2 : -2 * t ^ 2 / (h * v ^ 2 * σ ^ 2) = -(2 / (σ ^ 2 * h) / v ^ 2) * t ^ 2 := by
      have := hσ.ne'; have := hh.ne'; have := hv0.ne'
      field_simp
    rw [e2]
    field_simp
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    have := hu.1
    exact mul_nonneg (exp_pos _).le (Real.rpow_nonneg (by positivity) _)

lemma sqrt_K {σ h : ℝ} (hσ : 0 < σ) (hh : 0 < h) :
    √(π / (2 / (σ ^ 2 * h))) = σ * √h * √(2 * π) / 2 := by
  have e : π / (2 / (σ ^ 2 * h)) = (σ * √h * √(2 * π) / 2) ^ 2 := by
    rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt hh.le, Real.sq_sqrt (by positivity)]
    field_simp
  rw [e, Real.sqrt_sq (by positivity)]

open ProbabilityTheory RogersSatchell.Correction in
lemma tail_max {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {σ h : ℝ} {Z Z' : Ω → ℝ}
    (hZ : HasOvershootLaw P σ h Z) (hZ' : HasOvershootLaw P σ h Z') (hind : IndepFun Z Z' P)
    {t : ℝ} (ht : 0 ≤ t) :
    P.real {ω | t < max (Z ω) (Z' ω)} =
      2 * overshootSurvival σ h t - overshootSurvival σ h t ^ 2 := by
  have hA : P.real (Z ⁻¹' Iic t) = 1 - overshootSurvival σ h t := by
    have : Z ⁻¹' Iic t = {ω | t < Z ω}ᶜ := by ext; simp [not_lt]
    rw [this, probReal_compl_eq_one_sub (measurableSet_lt measurable_const hZ.1), hZ.2 t ht]
  have hB : P.real (Z' ⁻¹' Iic t) = 1 - overshootSurvival σ h t := by
    have : Z' ⁻¹' Iic t = {ω | t < Z' ω}ᶜ := by ext; simp [not_lt]
    rw [this, probReal_compl_eq_one_sub (measurableSet_lt measurable_const hZ'.1), hZ'.2 t ht]
  have hset : {ω | t < max (Z ω) (Z' ω)} = (Z ⁻¹' Iic t ∩ Z' ⁻¹' Iic t)ᶜ := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_Iic, lt_max_iff, not_and_or, not_le]
  have hmul : P.real (Z ⁻¹' Iic t ∩ Z' ⁻¹' Iic t) =
      P.real (Z ⁻¹' Iic t) * P.real (Z' ⁻¹' Iic t) := by
    simp only [measureReal_def]
    rw [hind.measure_inter_preimage_eq_mul _ _ measurableSet_Iic measurableSet_Iic,
      ENNReal.toReal_mul]
  rw [hset, probReal_compl_eq_one_sub ((hZ.1 measurableSet_Iic).inter (hZ'.1 measurableSet_Iic)),
    hmul, hA, hB]
  ring

end RSOvershoot

open MeasureTheory ProbabilityTheory RogersSatchell.Correction in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (σ h : ℝ) (hσ : 0 < σ) (hh : 0 < h) (Z Z' : Ω → ℝ)
    (hZ : HasOvershootLaw P σ h Z) (hZ' : HasOvershootLaw P σ h Z') (hind : IndepFun Z Z' P) :
    Integrable (fun ω => max (Z ω) (Z' ω)) P ∧
      Integrable (fun ω => max (Z ω) (Z' ω) ^ 2) P ∧
      ∫ ω, max (Z ω) (Z' ω) ∂P = constA * σ * Real.sqrt h ∧
      ∫ ω, max (Z ω) (Z' ω) ^ 2 ∂P = constB * σ ^ 2 * h := by
  obtain ⟨c, hc_def⟩ : ∃ c : ℝ, c = 2 / (σ ^ 2 * h) := ⟨_, rfl⟩
  have hc : 0 < c := by rw [hc_def]; positivity
  have hG : ∀ t, overshootSurvival σ h t = (RSOvershoot.ell c t).toReal := fun t => by
    rw [hc_def]; exact RSOvershoot.surv_eq hσ hh t
  have hfin : ∀ t, RSOvershoot.ell c t ≠ ⊤ := fun t =>
    (lt_of_le_of_lt (RSOvershoot.ell_le_one hc.le t) ENNReal.one_lt_top).ne
  have hG0 : ∀ t, 0 ≤ (RSOvershoot.ell c t).toReal := fun t => ENNReal.toReal_nonneg
  have hG1 : ∀ t, (RSOvershoot.ell c t).toReal ≤ 1 := fun t =>
    ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using RSOvershoot.ell_le_one hc.le t)
  have hm2 : Measurable fun t : ℝ => ENNReal.ofReal (2 * t) := by fun_prop
  have hs2 : (1:ℝ) ≤ √2 := by
    rw [show (1:ℝ) = √1 from Real.sqrt_one.symm]; exact Real.sqrt_le_sqrt (by norm_num)
  obtain ⟨i1, v1⟩ := RSOvershoot.pack (E := fun t => RSOvershoot.ell c t) (RSOvershoot.ell_meas c) hfin (by positivity) (RSOvershoot.M1 hc)
  obtain ⟨i2, v2⟩ := RSOvershoot.pack (E := fun t => RSOvershoot.ell c t * RSOvershoot.ell c t) ((RSOvershoot.ell_meas c).mul (RSOvershoot.ell_meas c))
    (fun t => ENNReal.mul_ne_top (hfin t) (hfin t))
    (mul_nonneg (by positivity) (by linarith)) (RSOvershoot.M3 hc)
  obtain ⟨i3, v3⟩ := RSOvershoot.pack (E := fun t => RSOvershoot.ell c t * ENNReal.ofReal (2 * t)) ((RSOvershoot.ell_meas c).mul hm2)
    (fun t => ENNReal.mul_ne_top (hfin t) ENNReal.ofReal_ne_top) (by positivity) (RSOvershoot.M2 hc)
  obtain ⟨i4, v4⟩ := RSOvershoot.pack (E := fun t => RSOvershoot.ell c t * RSOvershoot.ell c t * ENNReal.ofReal (2 * t))
    (((RSOvershoot.ell_meas c).mul (RSOvershoot.ell_meas c)).mul hm2)
    (fun t => ENNReal.mul_ne_top (ENNReal.mul_ne_top (hfin t) (hfin t)) ENNReal.ofReal_ne_top)
    (mul_nonneg (by positivity) (by linarith [Real.pi_le_four])) (RSOvershoot.M4 hc)
  -- positivity of `Z`
  have hpos : ∀ᵐ ω ∂P, 0 < Z ω := by
    have hm : MeasurableSet {ω | 0 < Z ω} := measurableSet_lt measurable_const hZ.1
    have h1 : P {ω | 0 < Z ω} = 1 := by
      have e := hZ.2 0 le_rfl
      rw [hG, RSOvershoot.ell_zero, ENNReal.toReal_one, measureReal_def, ENNReal.toReal_eq_one_iff] at e
      exact e
    rw [ae_iff]
    have := (prob_compl_eq_zero_iff hm).2 h1
    simpa [Set.compl_ofPred, not_lt] using this
  have hM_nn : 0 ≤ᵐ[P] (fun ω => max (Z ω) (Z' ω)) :=
    hpos.mono (fun ω hω => le_trans hω.le (le_max_left _ _))
  have hMm : Measurable (fun ω => max (Z ω) (Z' ω)) := hZ.1.max hZ'.1
  have htail : ∀ t ∈ Ioi (0:ℝ), P {ω | t < max (Z ω) (Z' ω)} =
      ENNReal.ofReal (2 * (RSOvershoot.ell c t).toReal - (RSOvershoot.ell c t).toReal ^ 2) := by
    intro t ht
    have e := RSOvershoot.tail_max hZ hZ' hind (le_of_lt ht)
    rw [hG] at e
    rw [← e, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  have hFnn : ∀ t, 0 ≤ 2 * (RSOvershoot.ell c t).toReal - (RSOvershoot.ell c t).toReal ^ 2 := fun t => by
    nlinarith [hG0 t, hG1 t]
  -- first moment
  have hFint : IntegrableOn (fun t => 2 * (RSOvershoot.ell c t).toReal - (RSOvershoot.ell c t).toReal ^ 2) (Ioi 0) := by
    refine IntegrableOn.congr_fun
      (f := fun t => 2 * (RSOvershoot.ell c t).toReal - (RSOvershoot.ell c t * RSOvershoot.ell c t).toReal)
      ((i1.const_mul 2).sub i2) (fun t _ => ?_) measurableSet_Ioi
    simp only [ENNReal.toReal_mul, sq]
  have hFval : ∫ t in Ioi (0:ℝ), (2 * (RSOvershoot.ell c t).toReal - (RSOvershoot.ell c t).toReal ^ 2) =
      2 * (√(π / c) / 2 * (1 / 2)) - √(π / c) / 2 * ((2 * √2 - 2) / 3) := by
    rw [← v1, ← v2, ← integral_const_mul, ← integral_sub (i1.const_mul 2) i2]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    simp only [ENNReal.toReal_mul, sq]
  have hFI0 : 0 ≤ ∫ t in Ioi (0:ℝ), (2 * (RSOvershoot.ell c t).toReal - (RSOvershoot.ell c t).toReal ^ 2) :=
    setIntegral_nonneg measurableSet_Ioi (fun t _ => hFnn t)
  have hlint1 : ∫⁻ ω, ENNReal.ofReal (max (Z ω) (Z' ω)) ∂P =
      ENNReal.ofReal (∫ t in Ioi (0:ℝ), (2 * (RSOvershoot.ell c t).toReal - (RSOvershoot.ell c t).toReal ^ 2)) := by
    rw [lintegral_eq_lintegral_meas_lt P hM_nn hMm.aemeasurable,
      setLIntegral_congr_fun measurableSet_Ioi htail]
    exact (ofReal_integral_eq_lintegral_ofReal hFint (Eventually.of_forall hFnn)).symm
  have hIM : Integrable (fun ω => max (Z ω) (Z' ω)) P := by
    have := integrable_toReal_of_lintegral_ne_top hMm.ennreal_ofReal.aemeasurable
      (by rw [hlint1]; exact ENNReal.ofReal_ne_top)
    refine this.congr ?_
    filter_upwards [hM_nn] with ω hω
    exact ENNReal.toReal_ofReal hω
  have hEM : ∫ ω, max (Z ω) (Z' ω) ∂P =
      ∫ t in Ioi (0:ℝ), (2 * (RSOvershoot.ell c t).toReal - (RSOvershoot.ell c t).toReal ^ 2) := by
    rw [integral_eq_lintegral_of_nonneg_ae hM_nn hMm.aestronglyMeasurable, hlint1,
      ENNReal.toReal_ofReal hFI0]
  -- second moment
  have hlc := lintegral_comp_eq_lintegral_meas_lt_mul P hM_nn hMm.aemeasurable
    (g := fun t => 2 * t)
    (fun t _ => (continuous_const.mul continuous_id).intervalIntegrable _ _)
    (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have : (0:ℝ) < t := ht
        positivity)
  have hsq : ∀ x : ℝ, ∫ t in (0:ℝ)..x, 2 * t = x ^ 2 := fun x => by
    rw [intervalIntegral.integral_const_mul, integral_id]; ring
  simp only [hsq] at hlc
  have hF2eq : EqOn (fun t => 2 * (RSOvershoot.ell c t * ENNReal.ofReal (2 * t)).toReal -
      (RSOvershoot.ell c t * RSOvershoot.ell c t * ENNReal.ofReal (2 * t)).toReal)
      (fun t => (2 * (RSOvershoot.ell c t).toReal - (RSOvershoot.ell c t).toReal ^ 2) * (2 * t)) (Ioi 0) := by
    intro t ht
    have : (0:ℝ) < t := ht
    simp only
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity)]
    ring
  have hF2int : IntegrableOn (fun t => (2 * (RSOvershoot.ell c t).toReal - (RSOvershoot.ell c t).toReal ^ 2) * (2 * t))
      (Ioi 0) := IntegrableOn.congr_fun
        (f := fun t => 2 * (RSOvershoot.ell c t * ENNReal.ofReal (2 * t)).toReal -
          (RSOvershoot.ell c t * RSOvershoot.ell c t * ENNReal.ofReal (2 * t)).toReal)
        ((i3.const_mul 2).sub i4) hF2eq measurableSet_Ioi
  have hF2val : ∫ t in Ioi (0:ℝ), (2 * (RSOvershoot.ell c t).toReal - (RSOvershoot.ell c t).toReal ^ 2) * (2 * t) =
      2 * (1 / c * (1 / 3)) - 1 / c * (1 / 2 - π / 8) := by
    rw [← v3, ← v4, ← integral_const_mul, ← integral_sub (i3.const_mul 2) i4]
    exact (setIntegral_congr_fun measurableSet_Ioi hF2eq).symm
  have hF2nn : ∀ t ∈ Ioi (0:ℝ), 0 ≤ (2 * (RSOvershoot.ell c t).toReal - (RSOvershoot.ell c t).toReal ^ 2) * (2 * t) :=
    fun t ht => by have : (0:ℝ) < t := ht; have := hFnn t; positivity
  have hF2I0 : 0 ≤ ∫ t in Ioi (0:ℝ), (2 * (RSOvershoot.ell c t).toReal - (RSOvershoot.ell c t).toReal ^ 2) * (2 * t) :=
    setIntegral_nonneg measurableSet_Ioi hF2nn
  have hlint2 : ∫⁻ ω, ENNReal.ofReal (max (Z ω) (Z' ω) ^ 2) ∂P =
      ENNReal.ofReal (∫ t in Ioi (0:ℝ), (2 * (RSOvershoot.ell c t).toReal - (RSOvershoot.ell c t).toReal ^ 2) * (2 * t)) := by
    rw [hlc]
    rw [ofReal_integral_eq_lintegral_ofReal hF2int
      (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht; exact hF2nn t ht)]
    refine setLIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    rw [htail t ht, ← ENNReal.ofReal_mul (hFnn t)]
  have hMm2 : Measurable (fun ω => max (Z ω) (Z' ω) ^ 2) := hMm.pow_const 2
  have hIM2 : Integrable (fun ω => max (Z ω) (Z' ω) ^ 2) P := by
    have := integrable_toReal_of_lintegral_ne_top hMm2.ennreal_ofReal.aemeasurable
      (by rw [hlint2]; exact ENNReal.ofReal_ne_top)
    refine this.congr (Eventually.of_forall (fun ω => ?_))
    exact ENNReal.toReal_ofReal (sq_nonneg _)
  have hEM2 : ∫ ω, max (Z ω) (Z' ω) ^ 2 ∂P =
      ∫ t in Ioi (0:ℝ), (2 * (RSOvershoot.ell c t).toReal - (RSOvershoot.ell c t).toReal ^ 2) * (2 * t) := by
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall (fun ω => sq_nonneg _))
      hMm2.aestronglyMeasurable, hlint2, ENNReal.toReal_ofReal hF2I0]
  refine ⟨hIM, hIM2, ?_, ?_⟩
  · rw [hEM, hFval, hc_def, RSOvershoot.sqrt_K hσ hh, constA]
    ring
  · rw [hEM2, hF2val, hc_def, constB]
    have := hσ.ne'; have := hh.ne'
    field_simp
    ring
