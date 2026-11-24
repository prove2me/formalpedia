-- Prove2me | solution 1 for SchoenfeldBRH.psi_bound_large_of_RH_low_count
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-11-24T02:20:36.065166+00:00
-- url     : https://prove2.me/submissions/cc0e6601-88c0-4407-a5bb-4e04282f38b7

import Definitions.Def_dusart_psi_433_20261014_SmoothedFormula
import Definitions.Def_dusart_psi_433_20261014_ZeroAbel
import Definitions.Def_dusart_psi_433_20261014_WeightedCount
import Theorems.Thm_ExplicitPNT_DusartTable1_Modules_PowerQuarterWeights
import Mathlib
import Theorems.Thm_TaoFivePrimes_zeta_ne_zero_strip_im_two_to_fourteen
import Theorems.Thm_zeta_ne_zero_of_mem_strip_of_abs_im_le_two

-- ===== K1 =====
section

open DusartSmoothing Complex

namespace SchoenfeldK

lemma norm_cpow_ofReal_pos (z : ℝ) (hz : 0 < z) (r : ℂ) : ‖((z : ℂ) ^ r)‖ = z ^ r.re :=
  Complex.norm_cpow_eq_rpow_re_of_pos hz r

/-- bound for the quadratic kernel by height -/
lemma norm_quadraticKernel_le (z : ℝ) (hz : 0 < z) (ρ : ℂ) (hi : 0 < |ρ.im|) :
    ‖quadraticKernel z ρ‖ ≤ z ^ (ρ.re + 2) / |ρ.im| ^ 3 := by
  unfold quadraticKernel
  rw [norm_div, norm_cpow_ofReal_pos z hz, norm_mul, norm_mul]
  have h0 : |ρ.im| ≤ ‖ρ‖ := Complex.abs_im_le_norm ρ
  have h1 : |ρ.im| ≤ ‖ρ + 1‖ := by
    have := Complex.abs_im_le_norm (ρ + 1); simpa using this
  have h2 : |ρ.im| ≤ ‖ρ + 2‖ := by
    have := Complex.abs_im_le_norm (ρ + 2); simpa using this
  have hre : (ρ + 2).re = ρ.re + 2 := by simp
  rw [hre]
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  calc |ρ.im| ^ 3 = |ρ.im| * |ρ.im| * |ρ.im| := by ring
    _ ≤ ‖ρ‖ * ‖ρ + 1‖ * ‖ρ + 2‖ := by gcongr

theorem kernel_bound_line (y h : ℝ) (hy : 1 ≤ y) (hh : 0 < h) (ρ : ℂ)
    (hre : ρ.re = 1 / 2) (hi : 0 < |ρ.im|) :
    ‖smoothedZeroKernel y h ρ‖ ≤
      Real.sqrt (y + 2 * h) * min (1 / |ρ.im|) ((2 * (y + 2 * h) / h) ^ 2 / |ρ.im| ^ 3) := by
  have hy0 : 0 < y := by linarith
  have hY : 0 < y + 2 * h := by linarith
  have hsq : 0 ≤ Real.sqrt (y + 2 * h) := Real.sqrt_nonneg _
  unfold smoothedZeroKernel
  rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh]
  have hh2 : 0 < h ^ 2 := by positivity
  rw [mul_min_of_nonneg _ _ hsq, le_min_iff]
  constructor
  · -- low bound
    have hp : ∀ z ∈ Set.Icc y (y + 2 * h), ‖((z : ℂ)) ^ ρ‖ ≤ Real.sqrt (y + 2 * h) := by
      intro z hz
      have hz0 : 0 < z := by linarith [hz.1]
      rw [norm_cpow_ofReal_pos z hz0, hre, ← Real.sqrt_eq_rpow]
      exact Real.sqrt_le_sqrt hz.2
    have hl := norm_quadraticKernel_second_difference_low y h (Real.sqrt (y + 2 * h)) hh hsq ρ
      (by rw [hre]; norm_num) hi hp
    rw [div_le_iff₀ hh2]
    calc _ ≤ h ^ 2 * Real.sqrt (y + 2 * h) / |ρ.im| := hl
      _ = _ := by ring
  · -- high bound
    have hq : ∀ z : ℝ, 0 < z → z ≤ y + 2 * h →
        ‖quadraticKernel z ρ‖ ≤ (y + 2 * h) ^ (5 / 2 : ℝ) / |ρ.im| ^ 3 := by
      intro z hz hzY
      calc _ ≤ z ^ (ρ.re + 2) / |ρ.im| ^ 3 := norm_quadraticKernel_le z hz ρ hi
        _ ≤ _ := by
          rw [hre]; norm_num
          gcongr
    have e1 := hq (y + 2 * h) hY le_rfl
    have e2 := hq (y + h) (by linarith) (by linarith)
    have e3 := hq y hy0 (by linarith)
    have htri : ‖quadraticKernel (y + 2 * h) ρ - 2 * quadraticKernel (y + h) ρ + quadraticKernel y ρ‖
        ≤ ‖quadraticKernel (y + 2 * h) ρ‖ + 2 * ‖quadraticKernel (y + h) ρ‖ + ‖quadraticKernel y ρ‖ := by
      calc _ ≤ ‖quadraticKernel (y + 2 * h) ρ - 2 * quadraticKernel (y + h) ρ‖ + ‖quadraticKernel y ρ‖ :=
            norm_add_le _ _
        _ ≤ _ := by
          gcongr
          calc _ ≤ ‖quadraticKernel (y + 2 * h) ρ‖ + ‖2 * quadraticKernel (y + h) ρ‖ := norm_sub_le _ _
            _ = _ := by rw [norm_mul]; norm_num
    rw [div_le_iff₀ hh2]
    have hpow : (y + 2 * h) ^ (5 / 2 : ℝ) = Real.sqrt (y + 2 * h) * (y + 2 * h) ^ 2 := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_add hY]; norm_num
    have hγ3 : 0 < |ρ.im| ^ 3 := by positivity
    calc _ ≤ 4 * ((y + 2 * h) ^ (5 / 2 : ℝ) / |ρ.im| ^ 3) := by linarith
      _ = _ := by
        rw [hpow]; field_simp; ring

end SchoenfeldK

end

-- ===== A1 =====
section

open Set MeasureTheory DusartSmoothing

namespace SchoenfeldAbel

/-- the kernel majorant `min (1/t) (θ²/t³)` -/
noncomputable def gk (θ t : ℝ) : ℝ := min (1 / t) (θ ^ 2 / t ^ 3)

/-- minus its derivative -/
noncomputable def dk (θ t : ℝ) : ℝ := if t ≤ θ then 1 / t ^ 2 else 3 * θ ^ 2 / t ^ 4

lemma gk_of_le {θ t : ℝ} (ht : 0 < t) (h : t ≤ θ) : gk θ t = 1 / t := by
  unfold gk
  apply min_eq_left
  rw [div_le_div_iff₀ ht (by positivity)]
  have : t ^ 2 ≤ θ ^ 2 := by gcongr
  nlinarith [sq_nonneg t]

lemma gk_of_ge {θ t : ℝ} (hθ : 0 < θ) (h : θ ≤ t) : gk θ t = θ ^ 2 / t ^ 3 := by
  have ht : 0 < t := lt_of_lt_of_le hθ h
  unfold gk
  apply min_eq_right
  rw [div_le_div_iff₀ (by positivity) ht]
  have : θ ^ 2 ≤ t ^ 2 := by gcongr
  nlinarith [sq_nonneg t]

lemma integral_inv_sq {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q) :
    ∫ t in p..q, 1 / t ^ 2 = 1 / p - 1 / q := by
  have hd : ∀ t ∈ uIcc p q, HasDerivAt (fun t : ℝ => -(1 / t)) (1 / t ^ 2) t := by
    intro t ht
    rw [uIcc_of_le hpq] at ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have e : (fun t : ℝ => -(1 / t)) = fun t => -t⁻¹ := by funext s; simp [one_div]
    rw [e]
    exact ((hasDerivAt_inv ht0).neg).congr_deriv (by rw [neg_neg, one_div])
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd]
  · ring
  · apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div continuousOn_const (continuousOn_pow 2)
    intro t ht; rw [uIcc_of_le hpq] at ht; have : 0 < t := by linarith [ht.1]
    positivity

lemma integral_quartic {p q θ : ℝ} (hp : 0 < p) (hpq : p ≤ q) :
    ∫ t in p..q, 3 * θ ^ 2 / t ^ 4 = θ ^ 2 / p ^ 3 - θ ^ 2 / q ^ 3 := by
  have hd : ∀ t ∈ uIcc p q, HasDerivAt (fun t : ℝ => -(θ ^ 2 / t ^ 3)) (3 * θ ^ 2 / t ^ 4) t := by
    intro t ht
    rw [uIcc_of_le hpq] at ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have h1 : HasDerivAt (fun t : ℝ => t ^ 3) (3 * t ^ 2) t := by
      simpa using hasDerivAt_pow 3 t
    have e : (fun t : ℝ => -(θ ^ 2 / t ^ 3)) = fun t => -(θ ^ 2 * (t ^ 3)⁻¹) := by
      funext s; simp [div_eq_mul_inv]
    rw [e]
    refine (((h1.inv (pow_ne_zero 3 ht0)).const_mul (θ ^ 2)).neg).congr_deriv ?_
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd]
  · ring
  · apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div continuousOn_const (continuousOn_pow 4)
    intro t ht; rw [uIcc_of_le hpq] at ht; have : 0 < t := by linarith [ht.1]
    positivity

lemma dk_intervalIntegrable {θ p q : ℝ} (hp : 0 < p) (hpq : p ≤ q) :
    IntervalIntegrable (dk θ) volume p q := by
  have hm : Measurable (dk θ) := by
    unfold dk
    refine Measurable.ite measurableSet_Iic (by fun_prop) (by fun_prop)
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hpq]
  refine Measure.integrableOn_of_bounded (M := 1 / p ^ 2 + 3 * θ ^ 2 / p ^ 4)
    (by simp [Real.volume_Icc]) hm.aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Icc]
  filter_upwards with t ht
  have ht0 : 0 < t := by linarith [ht.1]
  have h1 : 1 / t ^ 2 ≤ 1 / p ^ 2 := by gcongr; exact ht.1
  have h2 : 3 * θ ^ 2 / t ^ 4 ≤ 3 * θ ^ 2 / p ^ 4 := by gcongr; exact ht.1
  have hn1 : 0 ≤ 1 / t ^ 2 := by positivity
  have hn2 : 0 ≤ 3 * θ ^ 2 / t ^ 4 := by positivity
  have hp1 : 0 ≤ 1 / p ^ 2 := by positivity
  have hp2 : 0 ≤ 3 * θ ^ 2 / p ^ 4 := by positivity
  unfold dk
  rw [Real.norm_eq_abs]
  split_ifs
  · rw [abs_of_nonneg hn1]; linarith
  · rw [abs_of_nonneg hn2]; linarith

/-- fundamental theorem of calculus for the piecewise majorant -/
lemma gk_sub_eq_integral {θ c b : ℝ} (hc : 0 < c) (hcb : c ≤ b) (hθ : 0 < θ) (hθb : θ ≤ b) :
    gk θ c - gk θ b = ∫ t in c..b, dk θ t := by
  rw [gk_of_ge hθ hθb]
  rcases le_total c θ with h | h
  · rw [gk_of_le hc h,
      ← intervalIntegral.integral_add_adjacent_intervals (b := θ)
        (dk_intervalIntegrable hc h) (dk_intervalIntegrable (by linarith) hθb)]
    have e1 : ∫ t in c..θ, dk θ t = ∫ t in c..θ, 1 / t ^ 2 := by
      apply intervalIntegral.integral_congr
      intro t ht; rw [uIcc_of_le h] at ht
      simp [dk, ht.2]
    have e2 : ∫ t in θ..b, dk θ t = ∫ t in θ..b, 3 * θ ^ 2 / t ^ 4 := by
      apply intervalIntegral.integral_congr_Ioo_of_le hθb
      intro t ht
      simp [dk, not_le.mpr ht.1]
    rw [e1, e2, integral_inv_sq hc h, integral_quartic hθ hθb]
    field_simp
    ring
  · rw [gk_of_ge hθ h]
    have e2 : ∫ t in c..b, dk θ t = ∫ t in c..b, 3 * θ ^ 2 / t ^ 4 := by
      apply intervalIntegral.integral_congr_Ioo_of_le hcb
      intro t ht
      simp [dk, not_le.mpr (lt_of_le_of_lt h ht.1)]
    rw [e2, integral_quartic hc hcb]

lemma dk_nonneg (θ t : ℝ) : 0 ≤ dk θ t := by
  unfold dk; split_ifs <;> positivity

lemma primeStep_measurable (c : ℝ) : Measurable (primeStep c) := by
  unfold primeStep
  exact Measurable.ite measurableSet_Ici measurable_const measurable_const

lemma dk_measurable (θ : ℝ) : Measurable (dk θ) := by
  unfold dk
  exact Measurable.ite measurableSet_Iic (by fun_prop) (by fun_prop)

lemma ps_dk_int {θ p q c : ℝ} (hp : 0 < p) (hpq : p ≤ q) :
    IntervalIntegrable (fun t => primeStep c t * dk θ t) volume p q := by
  refine (dk_intervalIntegrable (θ := θ) hp hpq).mono_fun'
    ((primeStep_measurable c).mul (dk_measurable θ)).aestronglyMeasurable ?_
  filter_upwards with t
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by unfold primeStep; split_ifs <;> norm_num)
    (dk_nonneg θ t))]
  have : primeStep c t ≤ 1 := by unfold primeStep; split_ifs <;> norm_num
  nlinarith [dk_nonneg θ t]

lemma integral_primeStep_dk {θ a b c : ℝ} (ha : 0 < a) (hac : a ≤ c) (hcb : c ≤ b) :
    ∫ t in a..b, primeStep c t * dk θ t = ∫ t in c..b, dk θ t := by
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := c)
    (ps_dk_int ha hac) (ps_dk_int (by linarith) hcb)]
  have e1 : ∫ t in a..c, primeStep c t * dk θ t = 0 := by
    calc _ = ∫ _ in a..c, (0 : ℝ) := by
          apply intervalIntegral.integral_congr_Ioo_of_le hac
          intro t ht
          simp only [primeStep, if_neg (not_le.mpr ht.2), zero_mul]
      _ = 0 := intervalIntegral.integral_zero
  have e2 : ∫ t in c..b, primeStep c t * dk θ t = ∫ t in c..b, dk θ t := by
    apply intervalIntegral.integral_congr
    intro t ht; rw [uIcc_of_le hcb] at ht
    simp only [primeStep, if_pos ht.1, one_mul]
  rw [e1, e2, zero_add]

/-- Abel summation identity for the piecewise kernel majorant. -/
theorem abel_gk {α : Type*} (Z : Finset α) (m : α → ℕ) (γ : α → ℝ) {θ a b : ℝ}
    (ha : 0 < a) (haθ : a ≤ θ) (hθb : θ ≤ b)
    (hγ : ∀ ρ ∈ Z, a ≤ γ ρ ∧ γ ρ ≤ b) :
    (∑ ρ ∈ Z, (m ρ : ℝ) * gk θ (γ ρ)) =
      gk θ b * (∑ ρ ∈ Z, (m ρ : ℝ)) + ∫ t in a..b, finiteZeroCount Z m γ t * dk θ t := by
  have hθ : 0 < θ := lt_of_lt_of_le ha haθ
  have hab : a ≤ b := haθ.trans hθb
  have hterm : ∀ ρ ∈ Z, (m ρ : ℝ) * gk θ (γ ρ) =
      (m ρ : ℝ) * gk θ b + ∫ t in a..b, (m ρ : ℝ) * primeStep (γ ρ) t * dk θ t := by
    intro ρ hρ
    obtain ⟨h1, h2⟩ := hγ ρ hρ
    have e := gk_sub_eq_integral (θ := θ) (lt_of_lt_of_le ha h1) h2 hθ hθb
    have e2 := integral_primeStep_dk (θ := θ) ha h1 h2
    have e3 : ∫ t in a..b, (m ρ : ℝ) * primeStep (γ ρ) t * dk θ t =
        (m ρ : ℝ) * ∫ t in a..b, primeStep (γ ρ) t * dk θ t := by
      rw [← intervalIntegral.integral_const_mul]
      congr 1; funext t; ring
    rw [e3, e2, ← e]
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.sum_mul, mul_comm]
  congr 1
  have hint : ∀ ρ ∈ Z, IntervalIntegrable
      (fun t => (m ρ : ℝ) * primeStep (γ ρ) t * dk θ t) volume a b := by
    intro ρ _
    have := (ps_dk_int (θ := θ) (c := γ ρ) ha hab).const_mul (m ρ : ℝ)
    simpa [mul_assoc] using this
  rw [← intervalIntegral.integral_finsetSum hint]
  congr 1
  funext t
  unfold finiteZeroCount
  rw [Finset.sum_mul]

/-- Abel summation inequality with a counting majorant. -/
theorem abel_gk_le {α : Type*} (Z : Finset α) (m : α → ℕ) (γ : α → ℝ) {θ a b : ℝ}
    (ha : 0 < a) (haθ : a ≤ θ) (hθb : θ ≤ b)
    (hγ : ∀ ρ ∈ Z, a ≤ γ ρ ∧ γ ρ ≤ b) (W : ℝ → ℝ)
    (hW : ∀ t ∈ Icc a b, finiteZeroCount Z m γ t ≤ W t)
    (hWi : IntervalIntegrable (fun t => W t * dk θ t) volume a b) :
    (∑ ρ ∈ Z, (m ρ : ℝ) * gk θ (γ ρ)) ≤
      gk θ b * (∑ ρ ∈ Z, (m ρ : ℝ)) + ∫ t in a..b, W t * dk θ t := by
  rw [abel_gk Z m γ ha haθ hθb hγ]
  have hab : a ≤ b := haθ.trans hθb
  gcongr
  apply intervalIntegral.integral_mono_on hab
  · -- integrability of N * dk
    have hint : ∀ ρ ∈ Z, IntervalIntegrable
        (fun t => (m ρ : ℝ) * primeStep (γ ρ) t * dk θ t) volume a b := by
      intro ρ _
      have := (ps_dk_int (θ := θ) (c := γ ρ) ha hab).const_mul (m ρ : ℝ)
      simpa [mul_assoc] using this
    have hfun : (fun t => finiteZeroCount Z m γ t * dk θ t) =
        ∑ ρ ∈ Z, (fun t => (m ρ : ℝ) * primeStep (γ ρ) t * dk θ t) := by
      funext t
      unfold finiteZeroCount
      rw [Finset.sum_mul, Finset.sum_apply]
    rw [hfun]
    exact IntervalIntegrable.sum Z hint
  · exact hWi
  · intro t ht
    exact mul_le_mul_of_nonneg_right (hW t ht) (dk_nonneg θ t)

end SchoenfeldAbel

end

-- ===== A2 =====
section

open Set MeasureTheory DusartSmoothing Real

namespace SchoenfeldAbel

noncomputable def cM (t : ℝ) : ℝ := t / (2 * π) * (log (t / (2 * π)) - 1)

lemma cM_eq (t : ℝ) : cM t = DusartSmoothing.RvM.countingMain t := rfl

lemma hasDerivAt_logdiv {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun t : ℝ => log (t / (2 * π))) (1 / t) t := by
  have h2 : (0 : ℝ) < 2 * π := by positivity
  have := ((hasDerivAt_id t).div_const (2 * π)).log (by simp; positivity)
  refine this.congr_deriv ?_
  simp; field_simp

/-- D1 -/
lemma deriv_D1 {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun t : ℝ => (log (t / (2 * π)) - 1) ^ 2 / (4 * π)) (cM t / t ^ 2) t := by
  have := (((hasDerivAt_logdiv ht).sub_const 1).pow 2).div_const (4 * π)
  refine this.congr_deriv ?_
  unfold cM
  field_simp
  ring

/-- D2 -/
lemma deriv_D2 (θ : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun t : ℝ => -(3 * θ ^ 2 * (2 * log (t / (2 * π)) - 1) / (8 * π * t ^ 2)))
      (cM t * (3 * θ ^ 2 / t ^ 4)) t := by
  have h1 := (((hasDerivAt_logdiv ht).const_mul 2).sub_const 1).const_mul (3 * θ ^ 2)
  have h2 : HasDerivAt (fun t : ℝ => 8 * π * t ^ 2) (8 * π * (2 * t)) t := by
    have := (hasDerivAt_pow 2 t).const_mul (8 * π)
    simpa using this
  have := (h1.div h2 (by positivity)).neg
  refine this.congr_deriv ?_
  unfold cM
  field_simp
  ring

/-- D3 -/
lemma deriv_D3 {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun t : ℝ => -((9 * log t + 89) / t)) ((9 * log t + 80) / t ^ 2) t := by
  have h1 := ((hasDerivAt_log ht.ne').const_mul 9).add_const 89
  have := (h1.div (hasDerivAt_id t) ht.ne').neg
  refine this.congr_deriv ?_
  simp
  field_simp
  ring

/-- D4 -/
lemma deriv_D4 (θ : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun t : ℝ => -(θ ^ 2 * (9 * log t + 83) / t ^ 3))
      ((9 * log t + 80) * (3 * θ ^ 2 / t ^ 4)) t := by
  have h1 := (((hasDerivAt_log ht.ne').const_mul 9).add_const 83).const_mul (θ ^ 2)
  have h2 : HasDerivAt (fun t : ℝ => t ^ 3) (3 * t ^ 2) t := by simpa using hasDerivAt_pow 3 t
  have := (h1.div h2 (by positivity)).neg
  refine this.congr_deriv ?_
  field_simp
  ring


noncomputable def F1 (t : ℝ) : ℝ := (log (t / (2 * π)) - 1) ^ 2 / (4 * π)
noncomputable def F2 (θ t : ℝ) : ℝ := -(3 * θ ^ 2 * (2 * log (t / (2 * π)) - 1) / (8 * π * t ^ 2))
noncomputable def F3 (t : ℝ) : ℝ := -((9 * log t + 89) / t)
noncomputable def F4 (θ t : ℝ) : ℝ := -(θ ^ 2 * (9 * log t + 83) / t ^ 3)

noncomputable def W (t : ℝ) : ℝ := if t ≤ 2500 then cM t + 5 / 2 else cM t + 9 * log t + 80

lemma cont_log : ContinuousOn log (Ioi 0) := fun t ht => (continuousAt_log (ne_of_gt ht)).continuousWithinAt

lemma cM_contOn : ContinuousOn cM (Ioi 0) := by
  unfold cM
  apply ContinuousOn.mul (by fun_prop)
  apply ContinuousOn.sub _ continuousOn_const
  refine cont_log.comp (by fun_prop) ?_
  intro t ht; simp only [mem_Ioi] at ht ⊢; positivity

lemma uIcc_sub {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q) : uIcc p q ⊆ Ioi 0 := by
  rw [uIcc_of_le hpq]; intro t ht; exact lt_of_lt_of_le hp ht.1

lemma pos_of_uIcc {p q t : ℝ} (hp : 0 < p) (hpq : p ≤ q) (ht : t ∈ uIcc p q) : 0 < t :=
  uIcc_sub hp hpq ht

lemma ftc_Ioo {f F f' : ℝ → ℝ} {p q : ℝ} (hpq : p ≤ q)
    (heq : ∀ t ∈ Ioo p q, f t = f' t) (hd : ∀ t ∈ uIcc p q, HasDerivAt F (f' t) t)
    (hc : ContinuousOn f' (uIcc p q)) :
    IntervalIntegrable f volume p q ∧ ∫ t in p..q, f t = F q - F p := by
  constructor
  · rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hpq]
    have h1 : IntegrableOn f' (Ioo p q) volume := by
      have := hc.integrableOn_Icc (μ := volume)
      rw [min_eq_left hpq, max_eq_right hpq] at this
      exact this.mono_set Ioo_subset_Icc_self
    exact h1.congr_fun (fun t ht => (heq t ht).symm) measurableSet_Ioo
  · rw [intervalIntegral.integral_congr_Ioo_of_le hpq heq]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable

lemma contOn_quartic (θ : ℝ) {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q) :
    ContinuousOn (fun t : ℝ => 3 * θ ^ 2 / t ^ 4) (uIcc p q) :=
  continuousOn_const.div (by fun_prop) (fun t ht => by have := pos_of_uIcc hp hpq ht; positivity)

lemma contOn_log9 {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q) :
    ContinuousOn (fun t : ℝ => 9 * log t + 80) (uIcc p q) :=
  (continuousOn_const.mul (cont_log.mono (uIcc_sub hp hpq))).add continuousOn_const

lemma contOn_cM {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q) : ContinuousOn cM (uIcc p q) :=
  cM_contOn.mono (uIcc_sub hp hpq)

lemma hasDerivAt_quartic (θ : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun t : ℝ => -(θ ^ 2 / t ^ 3)) (3 * θ ^ 2 / t ^ 4) t := by
  have h1 : HasDerivAt (fun t : ℝ => t ^ 3) (3 * t ^ 2) t := by simpa using hasDerivAt_pow 3 t
  have e : (fun t : ℝ => -(θ ^ 2 / t ^ 3)) = fun t => -(θ ^ 2 * (t ^ 3)⁻¹) := by
    funext s; simp [div_eq_mul_inv]
  rw [e]
  refine (((h1.inv (pow_ne_zero 3 ht.ne')).const_mul (θ ^ 2)).neg).congr_deriv ?_
  field_simp

/-- piece on `[p,q]` with `q ≤ 2500` and `q ≤ θ` -/
lemma piece1 {θ p q : ℝ} (hp : 14 ≤ p) (hpq : p ≤ q) (hq : q ≤ 2500) (hqθ : q ≤ θ) :
    IntervalIntegrable (fun t => W t * dk θ t) volume p q ∧
    ∫ t in p..q, W t * dk θ t = (F1 q - F1 p) + 5 / 2 * (1 / p - 1 / q) := by
  have hp0 : 0 < p := by linarith
  have := ftc_Ioo (f := fun t => W t * dk θ t)
    (F := fun t => F1 t + 5 / 2 * (-(1 / t)))
    (f' := fun t => cM t / t ^ 2 + 5 / 2 * (1 / t ^ 2)) hpq ?_ ?_ ?_
  · refine ⟨this.1, ?_⟩; rw [this.2]; ring
  · intro t ht
    have h1 : t ≤ 2500 := ht.2.le.trans hq
    have h2 : t ≤ θ := ht.2.le.trans hqθ
    simp only [W, dk, if_pos h1, if_pos h2]
    ring
  · intro t ht
    have ht0 := pos_of_uIcc hp0 hpq ht
    have h1 := deriv_D1 ht0
    have h2 : HasDerivAt (fun t : ℝ => -(1 / t)) (1 / t ^ 2) t := by
      have e : (fun t : ℝ => -(1 / t)) = fun t => -t⁻¹ := by funext s; simp [one_div]
      rw [e]
      exact ((hasDerivAt_inv ht0.ne').neg).congr_deriv (by rw [neg_neg, one_div])
    exact h1.add (h2.const_mul (5 / 2))
  · apply ContinuousOn.add
    · exact (contOn_cM hp0 hpq).div (by fun_prop)
        (fun t ht => by have := pos_of_uIcc hp0 hpq ht; positivity)
    · apply ContinuousOn.mul continuousOn_const
      exact continuousOn_const.div (by fun_prop)
        (fun t ht => by have := pos_of_uIcc hp0 hpq ht; positivity)

/-- piece on `[p,q]` with `θ ≤ p` and `q ≤ 2500` -/
lemma piece2 {θ p q : ℝ} (hp : 14 ≤ p) (hpq : p ≤ q) (hq : q ≤ 2500) (hθp : θ ≤ p) :
    IntervalIntegrable (fun t => W t * dk θ t) volume p q ∧
    ∫ t in p..q, W t * dk θ t = (F2 θ q - F2 θ p) + 5 / 2 * (θ ^ 2 / p ^ 3 - θ ^ 2 / q ^ 3) := by
  have hp0 : 0 < p := by linarith
  have := ftc_Ioo (f := fun t => W t * dk θ t)
    (F := fun t => F2 θ t + 5 / 2 * (-(θ ^ 2 / t ^ 3)))
    (f' := fun t => cM t * (3 * θ ^ 2 / t ^ 4) + 5 / 2 * (3 * θ ^ 2 / t ^ 4)) hpq ?_ ?_ ?_
  · refine ⟨this.1, ?_⟩; rw [this.2]; ring
  · intro t ht
    have h1 : t ≤ 2500 := ht.2.le.trans hq
    have h2 : ¬ t ≤ θ := not_le.mpr (lt_of_le_of_lt hθp ht.1)
    simp only [W, dk, if_pos h1, if_neg h2]
    ring
  · intro t ht
    have ht0 := pos_of_uIcc hp0 hpq ht
    exact (deriv_D2 θ ht0).add ((hasDerivAt_quartic θ ht0).const_mul (5 / 2))
  · exact ((contOn_cM hp0 hpq).mul (contOn_quartic θ hp0 hpq)).add
      (continuousOn_const.mul (contOn_quartic θ hp0 hpq))

/-- piece on `[p,q]` with `2500 ≤ p` and `θ ≤ p` -/
lemma piece3 {θ p q : ℝ} (hp : 2500 ≤ p) (hpq : p ≤ q) (hθp : θ ≤ p) :
    IntervalIntegrable (fun t => W t * dk θ t) volume p q ∧
    ∫ t in p..q, W t * dk θ t = (F2 θ q - F2 θ p) + (F4 θ q - F4 θ p) := by
  have hp0 : 0 < p := by linarith
  have := ftc_Ioo (f := fun t => W t * dk θ t)
    (F := fun t => F2 θ t + F4 θ t)
    (f' := fun t => cM t * (3 * θ ^ 2 / t ^ 4) + (9 * log t + 80) * (3 * θ ^ 2 / t ^ 4)) hpq ?_ ?_ ?_
  · refine ⟨this.1, ?_⟩; rw [this.2]; ring
  · intro t ht
    have h1 : ¬ t ≤ 2500 := not_le.mpr (lt_of_le_of_lt hp ht.1)
    have h2 : ¬ t ≤ θ := not_le.mpr (lt_of_le_of_lt hθp ht.1)
    simp only [W, dk, if_neg h1, if_neg h2]
    ring
  · intro t ht
    have ht0 := pos_of_uIcc hp0 hpq ht
    exact (deriv_D2 θ ht0).add (deriv_D4 θ ht0)
  · exact ((contOn_cM hp0 hpq).mul (contOn_quartic θ hp0 hpq)).add
      ((contOn_log9 hp0 hpq).mul (contOn_quartic θ hp0 hpq))

/-- piece on `[p,q]` with `2500 ≤ p` and `q ≤ θ` -/
lemma piece4 {θ p q : ℝ} (hp : 2500 ≤ p) (hpq : p ≤ q) (hqθ : q ≤ θ) :
    IntervalIntegrable (fun t => W t * dk θ t) volume p q ∧
    ∫ t in p..q, W t * dk θ t = (F1 q - F1 p) + (F3 q - F3 p) := by
  have hp0 : 0 < p := by linarith
  have := ftc_Ioo (f := fun t => W t * dk θ t)
    (F := fun t => F1 t + F3 t)
    (f' := fun t => cM t / t ^ 2 + (9 * log t + 80) / t ^ 2) hpq ?_ ?_ ?_
  · refine ⟨this.1, ?_⟩; rw [this.2]; ring
  · intro t ht
    have h1 : ¬ t ≤ 2500 := not_le.mpr (lt_of_le_of_lt hp ht.1)
    have h2 : t ≤ θ := ht.2.le.trans hqθ
    simp only [W, dk, if_neg h1, if_pos h2]
    ring
  · intro t ht
    have ht0 := pos_of_uIcc hp0 hpq ht
    exact (deriv_D1 ht0).add (deriv_D3 ht0)
  · exact ((contOn_cM hp0 hpq).div (by fun_prop)
        (fun t ht => by have := pos_of_uIcc hp0 hpq ht; positivity)).add
      ((contOn_log9 hp0 hpq).div (by fun_prop)
        (fun t ht => by have := pos_of_uIcc hp0 hpq ht; positivity))


noncomputable def GA (θ : ℝ) : ℝ :=
  F1 θ - F1 14 + 5 / 28 + 3 * (2 * log (θ / (2 * π)) - 1) / (8 * π) + θ ^ 2 / 10 ^ 8

noncomputable def GB (θ : ℝ) : ℝ :=
  F1 θ - F1 14 + 5 / 28 + 638 / 10000 + 3 * (2 * log (θ / (2 * π)) - 1) / (8 * π) +
    (9 * log θ + 83) / θ

lemma log_2500_lt : log 2500 < 8 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  have h := Real.exp_one_gt_d9
  have : Real.exp 8 = Real.exp 1 ^ 8 := by rw [← Real.exp_nat_mul]; norm_num
  rw [this]
  calc (2500 : ℝ) < 2.7182818283 ^ 8 := by norm_num
    _ < _ := by gcongr

lemma log_ge_one_of_ge {b : ℝ} (hb : 2500 ≤ b) : 1 ≤ log (b / (2 * π)) := by
  rw [Real.le_log_iff_exp_le (by positivity)]
  have h := Real.exp_one_lt_d9
  rw [le_div_iff₀ (by positivity)]
  have hp := Real.pi_lt_d2
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  nlinarith

lemma F2_nonpos (θ : ℝ) {b : ℝ} (hb : 2500 ≤ b) : F2 θ b ≤ 0 := by
  unfold F2
  have := log_ge_one_of_ge hb
  have hb0 : 0 < b := by linarith
  apply neg_nonpos.mpr
  apply div_nonneg _ (by positivity)
  apply mul_nonneg (by positivity); linarith

lemma F4_nonpos (θ : ℝ) {b : ℝ} (hb : 1 ≤ b) : F4 θ b ≤ 0 := by
  unfold F4
  have := Real.log_nonneg hb
  apply neg_nonpos.mpr
  apply div_nonneg _ (by positivity)
  apply mul_nonneg (by positivity); linarith

lemma integral_bound_A {θ b : ℝ} (h14 : 14 ≤ θ) (hθ : θ ≤ 2500) (hb : 2500 ≤ b) :
    IntervalIntegrable (fun t => W t * dk θ t) volume 14 b ∧
    ∫ t in (14 : ℝ)..b, W t * dk θ t ≤ GA θ := by
  obtain ⟨i1, e1⟩ := piece1 (θ := θ) (p := 14) (q := θ) le_rfl h14 hθ le_rfl
  obtain ⟨i2, e2⟩ := piece2 (θ := θ) (p := θ) (q := 2500) h14 hθ le_rfl le_rfl
  obtain ⟨i3, e3⟩ := piece3 (θ := θ) (p := 2500) (q := b) le_rfl hb hθ
  refine ⟨(i1.trans i2).trans i3, ?_⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals (i1.trans i2) i3,
    ← intervalIntegral.integral_add_adjacent_intervals i1 i2, e1, e2, e3]
  have hF2 := F2_nonpos θ hb
  have hF4 := F4_nonpos θ (by linarith : (1 : ℝ) ≤ b)
  have hθ0 : 0 < θ := by linarith
  have hF2θ : F2 θ θ = -(3 * (2 * log (θ / (2 * π)) - 1) / (8 * π)) := by
    unfold F2; field_simp
  have hF4c : -F4 θ 2500 ≤ θ ^ 2 / 10 ^ 8 := by
    unfold F4
    have := log_2500_lt
    have hl : 0 ≤ log (2500 : ℝ) := Real.log_nonneg (by norm_num)
    rw [neg_neg, div_le_div_iff₀ (by norm_num) (by norm_num)]
    have : 0 ≤ θ ^ 2 := sq_nonneg θ
    nlinarith
  have hcube : θ ^ 2 / θ ^ 3 = 1 / θ := by field_simp
  have hpos : 0 ≤ θ ^ 2 / 2500 ^ 3 := by positivity
  unfold GA
  rw [hF2θ, hcube] at *
  nlinarith

lemma integral_bound_B {θ b : ℝ} (hθ : 2500 ≤ θ) (hb : θ ≤ b) :
    IntervalIntegrable (fun t => W t * dk θ t) volume 14 b ∧
    ∫ t in (14 : ℝ)..b, W t * dk θ t ≤ GB θ := by
  obtain ⟨i1, e1⟩ := piece1 (θ := θ) (p := 14) (q := 2500) (by norm_num) (by norm_num) le_rfl hθ
  obtain ⟨i2, e2⟩ := piece4 (θ := θ) (p := 2500) (q := θ) le_rfl hθ le_rfl
  obtain ⟨i3, e3⟩ := piece3 (θ := θ) (p := θ) (q := b) hθ hb le_rfl
  refine ⟨(i1.trans i2).trans i3, ?_⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals (i1.trans i2) i3,
    ← intervalIntegral.integral_add_adjacent_intervals i1 i2, e1, e2, e3]
  have hF2 := F2_nonpos θ (hθ.trans hb)
  have hF4 := F4_nonpos θ (by linarith : (1 : ℝ) ≤ b)
  have hθ0 : 0 < θ := by linarith
  have hF2θ : F2 θ θ = -(3 * (2 * log (θ / (2 * π)) - 1) / (8 * π)) := by
    unfold F2; field_simp
  have hF4θ : F4 θ θ = -((9 * log θ + 83) / θ) := by
    unfold F4; field_simp
  have hF3θ : F3 θ ≤ 0 := by
    unfold F3
    have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ θ)
    apply neg_nonpos.mpr; apply div_nonneg _ hθ0.le; linarith
  have hF3c : -F3 2500 ≤ 638 / 10000 + 1 / 1000 := by
    unfold F3
    have := log_2500_lt
    rw [neg_neg]
    rw [div_le_iff₀ (by norm_num)]
    nlinarith
  unfold GB
  rw [hF2θ, hF4θ] at *
  nlinarith

end SchoenfeldAbel

end

-- ===== A3 =====
section

open Set MeasureTheory DusartSmoothing Real

namespace SchoenfeldAbel

noncomputable def Gθ (θ : ℝ) : ℝ := if θ ≤ 2500 then GA θ else GB θ

lemma count_le_W
    (hlow : ∀ t : ℝ, 14 ≤ t → t ≤ 2500 → (RvM.Ncount 4 t : ℝ) ≤ RvM.countingMain t + 5 / 2)
    (Z : Finset ℂ) (hZ : ∀ ρ ∈ Z, RvM.IsNontrivialZero ρ ∧ 0 < ρ.im) (t : ℝ) (ht : 14 ≤ t) :
    finiteZeroCount Z RvM.zeroMult Complex.im t ≤ W t := by
  have h0 := finite_actual_zero_count_le Z hZ t
  rw [RvM.Ncount_zero_eq_four] at h0
  unfold W
  split_ifs with h
  · exact h0.trans (hlow t ht h)
  · have he := (abs_le.mp (RvM.positive_zero_count_error t (by linarith))).2
    rw [RvM.Ncount_zero_eq_four] at he
    have ht0 : 0 < t := by linarith
    have hl : log (t + 5) ≤ log t + 1 / 9 := by
      have : log (t + 5) - log t = log ((t + 5) / t) := by
        rw [Real.log_div (by linarith) ht0.ne']
      have h2 := Real.log_le_sub_one_of_pos (by positivity : 0 < (t + 5) / t)
      have h3 : (t + 5) / t - 1 ≤ 1 / 9 := by
        rw [div_sub_one ht0.ne', div_le_iff₀ ht0]; push Not at h; linarith
      linarith
    rw [← cM_eq] at he
    linarith

lemma W_le_sq {b : ℝ} (hb : 2500 ≤ b) : W b ≤ 2 * b ^ 2 := by
  have hb0 : 0 < b := by linarith
  have hl := Real.log_le_sub_one_of_pos hb0
  have hπ : 1 ≤ 2 * π := by linarith [Real.pi_gt_three]
  have hr : b / (2 * π) ≤ b := div_le_self hb0.le hπ
  have hl2 : log (b / (2 * π)) ≤ b := by
    have := Real.log_le_sub_one_of_pos (by positivity : 0 < b / (2 * π)); linarith
  have hc : cM b ≤ b ^ 2 := by
    unfold cM
    calc b / (2 * π) * (log (b / (2 * π)) - 1) ≤ b * b := by
          apply mul_le_mul hr (by linarith) _ hb0.le
          linarith [log_ge_one_of_ge hb]
      _ = b ^ 2 := by ring
  unfold W
  split_ifs <;> nlinarith

/-- the sum over a finite set of positive-height zeros -/
theorem pos_zero_sum_bound
    (hlow : ∀ t : ℝ, 14 ≤ t → t ≤ 2500 → (RvM.Ncount 4 t : ℝ) ≤ RvM.countingMain t + 5 / 2)
    (h14 : ∀ ρ : ℂ, RvM.IsNontrivialZero ρ → 0 < ρ.im → 14 ≤ ρ.im)
    {θ : ℝ} (hθ : 14 ≤ θ) (Z : Finset ℂ) (hZ : ∀ ρ ∈ Z, RvM.IsNontrivialZero ρ ∧ 0 < ρ.im) :
    (∑ ρ ∈ Z, (RvM.zeroMult ρ : ℝ) * gk θ ρ.im) ≤ Gθ θ + 1 / 100 := by
  have hθ0 : 0 < θ := by linarith
  set b : ℝ := 2500 + θ + 300 * θ ^ 2 + ∑ ρ ∈ Z, |ρ.im| with hbdef
  have hsum0 : 0 ≤ ∑ ρ ∈ Z, |ρ.im| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hb1 : 2500 ≤ b := by nlinarith [sq_nonneg θ]
  have hb2 : θ ≤ b := by nlinarith [sq_nonneg θ]
  have hb3 : 300 * θ ^ 2 ≤ b := by nlinarith [sq_nonneg θ]
  have hγ : ∀ ρ ∈ Z, 14 ≤ ρ.im ∧ ρ.im ≤ b := by
    intro ρ hρ
    refine ⟨h14 ρ (hZ ρ hρ).1 (hZ ρ hρ).2, ?_⟩
    have : |ρ.im| ≤ ∑ ρ ∈ Z, |ρ.im| :=
      Finset.single_le_sum (f := fun ρ : ℂ => |ρ.im|) (fun _ _ => abs_nonneg _) hρ
    have := le_abs_self ρ.im
    have := sq_nonneg θ
    linarith
  have hcount : ∀ t ∈ Icc (14 : ℝ) b, finiteZeroCount Z RvM.zeroMult Complex.im t ≤ W t :=
    fun t ht => count_le_W hlow Z hZ t ht.1
  -- integral bound
  have hint : IntervalIntegrable (fun t => W t * dk θ t) volume 14 b ∧
      ∫ t in (14 : ℝ)..b, W t * dk θ t ≤ Gθ θ := by
    unfold Gθ
    split_ifs with h
    · exact integral_bound_A hθ h hb1
    · exact integral_bound_B (le_of_lt (not_le.mp h)) hb2
  have hA := abel_gk_le Z RvM.zeroMult Complex.im (by norm_num : (0 : ℝ) < 14) hθ hb2 hγ W hcount
    hint.1
  -- boundary term
  have hmass : (∑ ρ ∈ Z, (RvM.zeroMult ρ : ℝ)) ≤ W b := by
    have h := hcount b ⟨by linarith, le_rfl⟩
    have he : finiteZeroCount Z RvM.zeroMult Complex.im b = ∑ ρ ∈ Z, (RvM.zeroMult ρ : ℝ) := by
      unfold finiteZeroCount
      apply Finset.sum_congr rfl
      intro ρ hρ
      simp [primeStep, (hγ ρ hρ).2]
    linarith
  have hgb : gk θ b = θ ^ 2 / b ^ 3 := gk_of_ge hθ0 hb2
  have hb0 : 0 < b := by linarith
  have hbd : gk θ b * (∑ ρ ∈ Z, (RvM.zeroMult ρ : ℝ)) ≤ 1 / 100 := by
    rw [hgb]
    have hm0 : 0 ≤ ∑ ρ ∈ Z, (RvM.zeroMult ρ : ℝ) := Finset.sum_nonneg (fun _ _ => by positivity)
    calc θ ^ 2 / b ^ 3 * (∑ ρ ∈ Z, (RvM.zeroMult ρ : ℝ)) ≤ θ ^ 2 / b ^ 3 * (2 * b ^ 2) := by
          gcongr; exact hmass.trans (W_le_sq hb1)
      _ = 2 * θ ^ 2 / b := by field_simp
      _ ≤ 1 / 100 := by
          rw [div_le_div_iff₀ hb0 (by norm_num)]; nlinarith
  linarith [hint.2]


theorem zero_series_bound (hRH : ∀ ρ : ℂ, RvM.IsNontrivialZero ρ → ρ.re = 1 / 2)
    (hlow : ∀ t : ℝ, 14 ≤ t → t ≤ 2500 → (RvM.Ncount 4 t : ℝ) ≤ RvM.countingMain t + 5 / 2)
    (h14 : ∀ ρ : ℂ, RvM.IsNontrivialZero ρ → 0 < ρ.im → 14 ≤ ρ.im)
    (y h X : ℝ) (hy : 1 ≤ y) (hh : 0 < h) (hX : y + 2 * h ≤ X) (hθ : 14 ≤ 2 * X / h) :
    ‖∑' ρ : NontrivialZetaZero, (RvM.zeroMult ρ.val : ℂ) * smoothedZeroKernel y h ρ.val‖ ≤
      Real.sqrt X * (2 * (Gθ (2 * X / h) + 1 / 100)) := by
  classical
  set θ := 2 * X / h with hθdef
  set B := Gθ θ + 1 / 100
  have hfin : ∀ S : Finset NontrivialZetaZero,
      ∑ ρ ∈ S, ‖(RvM.zeroMult ρ.val : ℂ) * smoothedZeroKernel y h ρ.val‖ ≤
        Real.sqrt X * (2 * B) := by
    intro S
    let Z : Finset ℂ := S.image (fun ρ : NontrivialZetaZero => ρ.val)
    have hZ : ∀ ρ ∈ Z, RvM.IsNontrivialZero ρ := by
      intro ρ hρ
      obtain ⟨τ, _, he⟩ := Finset.mem_image.mp hρ
      exact he ▸ τ.property
    have hpos : ∀ Z : Finset ℂ, (∀ ρ ∈ Z, RvM.IsNontrivialZero ρ ∧ 0 < ρ.im) →
        (∑ ρ ∈ Z, (RvM.zeroMult ρ : ℝ) * gk θ ρ.im) ≤ B :=
      fun Z hZ => pos_zero_sum_bound hlow h14 hθ Z hZ
    have h2 := ExplicitPNT.DusartTable1.Modules.PowerQuarterWeights.1 (gk θ) B hpos Z hZ
    have hterm : ∀ ρ ∈ S, ‖(RvM.zeroMult ρ.val : ℂ) * smoothedZeroKernel y h ρ.val‖ ≤
        Real.sqrt X * ((RvM.zeroMult ρ.val : ℝ) * gk θ |ρ.val.im|) := by
      intro ρ _
      have hi : 0 < |ρ.val.im| := by
        have := RvM.nontrivial_zero_abs_height ρ.val ρ.property
        linarith [Real.pi_pos]
      have hk := SchoenfeldK.kernel_bound_line y h hy hh ρ.val (hRH ρ.val ρ.property) hi
      rw [norm_mul, Complex.norm_natCast]
      have hmono : Real.sqrt (y + 2 * h) * min (1 / |ρ.val.im|) ((2 * (y + 2 * h) / h) ^ 2 / |ρ.val.im| ^ 3)
          ≤ Real.sqrt X * gk θ |ρ.val.im| := by
        have hy2 : 0 ≤ y + 2 * h := by linarith
        apply mul_le_mul (Real.sqrt_le_sqrt hX) _ (le_min (by positivity) (by positivity))
          (Real.sqrt_nonneg _)
        unfold gk
        apply min_le_min le_rfl
        have : 2 * (y + 2 * h) / h ≤ θ := by rw [hθdef]; gcongr
        gcongr
      have : ‖smoothedZeroKernel y h ρ.val‖ ≤ Real.sqrt X * gk θ |ρ.val.im| := hk.trans hmono
      calc (RvM.zeroMult ρ.val : ℝ) * ‖smoothedZeroKernel y h ρ.val‖ ≤
            (RvM.zeroMult ρ.val : ℝ) * (Real.sqrt X * gk θ |ρ.val.im|) := by
            gcongr
        _ = _ := by ring
    calc _ ≤ ∑ ρ ∈ S, Real.sqrt X * ((RvM.zeroMult ρ.val : ℝ) * gk θ |ρ.val.im|) :=
          Finset.sum_le_sum hterm
      _ = Real.sqrt X * ∑ ρ ∈ Z, (RvM.zeroMult ρ : ℝ) * gk θ |ρ.im| := by
          rw [← Finset.mul_sum]
          congr 1
          rw [Finset.sum_image (fun a _ b _ he => Subtype.val_injective he)]
      _ ≤ _ := by gcongr
  have hsum : Summable (fun ρ : NontrivialZetaZero =>
      ‖(RvM.zeroMult ρ.val : ℂ) * smoothedZeroKernel y h ρ.val‖) :=
    summable_of_sum_le (fun _ => norm_nonneg _) hfin
  calc _ ≤ ∑' ρ : NontrivialZetaZero, ‖(RvM.zeroMult ρ.val : ℂ) * smoothedZeroKernel y h ρ.val‖ :=
        norm_tsum_le_tsum_norm hsum
    _ ≤ _ := Real.tsum_le_of_sum_le (fun _ => norm_nonneg _) hfin

end SchoenfeldAbel

end

-- ===== R1 =====
section

open DusartSmoothing Complex MeasureTheory

namespace SchoenfeldR

noncomputable def sL (t : ℝ) : ℂ := -(1 / 2 : ℂ) + t * I

lemma sL_re (t : ℝ) : (sL t).re = -1 / 2 := by simp [sL]; norm_num

lemma sL_ne0 (t : ℝ) : sL t ≠ 0 := by
  intro h; have := congrArg Complex.re h; simp [sL] at this
lemma sL_ne1 (t : ℝ) : sL t + 1 ≠ 0 := by
  intro h; have := congrArg Complex.re h; simp [sL] at this; norm_num at this
lemma sL_ne2 (t : ℝ) : sL t + 2 ≠ 0 := by
  intro h; have := congrArg Complex.re h; simp [sL] at this; norm_num at this

/-- second-difference integral representation off the right half-plane -/
lemma secdiff_integral (x h : ℝ) (ρ : ℂ) (hr : 0 < ρ.re + 1)
    (h0 : ρ ≠ 0) (h1 : ρ + 1 ≠ 0) (h2 : ρ + 2 ≠ 0) :
    quadraticKernel (x + 2 * h) ρ - 2 * quadraticKernel (x + h) ρ + quadraticKernel x ρ =
      ∫ u in (0 : ℝ)..h, ∫ v in (0 : ℝ)..h, ((x + u + v : ℝ) : ℂ)^ρ / ρ := by
  have he : (fun u : ℝ => ∫ v in (0 : ℝ)..h, ((x + u + v : ℝ) : ℂ)^ρ / ρ) =
      fun u => ((((x + h + u : ℝ) : ℂ)^(ρ + 1) -
        ((x + u : ℝ) : ℂ)^(ρ + 1)) / (ρ + 1)) / ρ := by
    funext u
    rw [intervalIntegral.integral_div, integral_shift_cpow (x + u) h ρ (by linarith)]
    congr 3
    congr 1
    ring
  have hr1 : 0 < (ρ + 1).re := by simp; linarith
  have hi0 : IntervalIntegrable (fun u : ℝ => ((x + u : ℝ) : ℂ)^(ρ + 1)) volume 0 h := by
    apply Continuous.intervalIntegrable
    exact (Complex.continuous_ofReal_cpow_const hr1).comp (by fun_prop)
  have hi1 : IntervalIntegrable (fun u : ℝ => ((x + h + u : ℝ) : ℂ)^(ρ + 1)) volume 0 h := by
    apply Continuous.intervalIntegrable
    exact (Complex.continuous_ofReal_cpow_const hr1).comp (by fun_prop)
  rw [he, intervalIntegral.integral_div, intervalIntegral.integral_div,
    intervalIntegral.integral_sub hi1 hi0,
    integral_shift_cpow (x + h) h (ρ + 1) (by simp; linarith),
    integral_shift_cpow x h (ρ + 1) (by simp; linarith)]
  rw [show x + h + h = x + 2 * h by ring, show ρ + 1 + 1 = ρ + 2 by ring]
  unfold quadraticKernel
  field_simp
  ring

lemma secdiff_low (y h : ℝ) (hy : 0 < y) (hh : 0 < h) (t : ℝ) :
    ‖quadraticKernel (y + 2 * h) (sL t) - 2 * quadraticKernel (y + h) (sL t) +
      quadraticKernel y (sL t)‖ ≤ h ^ 2 * (y ^ (-(1 / 2 : ℝ)) / ‖sL t‖) := by
  rw [secdiff_integral y h (sL t) (by rw [sL_re]; norm_num) (sL_ne0 t) (sL_ne1 t) (sL_ne2 t)]
  have hn : 0 < ‖sL t‖ := norm_pos_iff.mpr (sL_ne0 t)
  have hinner : ∀ u ∈ Set.uIoc (0 : ℝ) h,
      ‖∫ v in (0 : ℝ)..h, ((y + u + v : ℝ) : ℂ)^(sL t) / (sL t)‖ ≤
        y ^ (-(1 / 2 : ℝ)) / ‖sL t‖ * h := by
    intro u hu
    rw [Set.uIoc_of_le hh.le] at hu
    have hb : ∀ v ∈ Set.uIoc (0 : ℝ) h, ‖((y + u + v : ℝ) : ℂ)^(sL t) / (sL t)‖ ≤
        y ^ (-(1 / 2 : ℝ)) / ‖sL t‖ := by
      intro v hv
      rw [Set.uIoc_of_le hh.le] at hv
      have hz : 0 < y + u + v := by linarith [hu.1, hv.1]
      rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hz, sL_re]
      apply div_le_div_of_nonneg_right _ hn.le
      rw [show (-1 / 2 : ℝ) = -(1 / 2) by norm_num]
      exact Real.rpow_le_rpow_of_nonpos hy (by linarith [hu.1, hv.1]) (by norm_num)
    have hb' := intervalIntegral.norm_integral_le_of_norm_le_const hb
    simpa only [sub_zero, abs_of_pos hh] using hb'
  have hh' := intervalIntegral.norm_integral_le_of_norm_le_const hinner
  rw [sub_zero, abs_of_pos hh] at hh'
  exact hh'.trans_eq (by ring)

lemma quadK_norm (z : ℝ) (hz : 0 < z) (t : ℝ) :
    ‖quadraticKernel z (sL t)‖ = z ^ (3 / 2 : ℝ) / (‖sL t‖ * ‖sL t + 1‖ * ‖sL t + 2‖) := by
  unfold quadraticKernel
  rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hz, norm_mul, norm_mul]
  congr 2
  simp [sL]; norm_num

lemma secdiff_high (y h : ℝ) (hy : 0 < y) (hh : 0 < h) (t : ℝ) :
    ‖quadraticKernel (y + 2 * h) (sL t) - 2 * quadraticKernel (y + h) (sL t) +
      quadraticKernel y (sL t)‖ ≤
        4 * (y + 2 * h) ^ (3 / 2 : ℝ) / (‖sL t‖ * ‖sL t + 1‖ * ‖sL t + 2‖) := by
  set d := ‖sL t‖ * ‖sL t + 1‖ * ‖sL t + 2‖
  have hd : 0 < d := by
    have a0 := norm_pos_iff.mpr (sL_ne0 t)
    have a1 := norm_pos_iff.mpr (sL_ne1 t)
    have a2 := norm_pos_iff.mpr (sL_ne2 t)
    positivity
  have hq : ∀ z : ℝ, 0 < z → z ≤ y + 2 * h → ‖quadraticKernel z (sL t)‖ ≤ (y + 2 * h) ^ (3 / 2 : ℝ) / d := by
    intro z hz hzY
    rw [quadK_norm z hz t]
    gcongr
  have e1 := hq (y + 2 * h) (by linarith) le_rfl
  have e2 := hq (y + h) (by linarith) (by linarith)
  have e3 := hq y hy (by linarith)
  calc _ ≤ ‖quadraticKernel (y + 2 * h) (sL t) - 2 * quadraticKernel (y + h) (sL t)‖ +
        ‖quadraticKernel y (sL t)‖ := norm_add_le _ _
    _ ≤ ‖quadraticKernel (y + 2 * h) (sL t)‖ + 2 * ‖quadraticKernel (y + h) (sL t)‖ +
        ‖quadraticKernel y (sL t)‖ := by
        gcongr
        calc _ ≤ ‖quadraticKernel (y + 2 * h) (sL t)‖ + ‖2 * quadraticKernel (y + h) (sL t)‖ :=
              norm_sub_le _ _
          _ = _ := by rw [norm_mul]; norm_num
    _ ≤ _ := by
        have : 4 * (y + 2 * h) ^ (3 / 2 : ℝ) / d = 4 * ((y + 2 * h) ^ (3 / 2 : ℝ) / d) := by ring
        rw [this]; linarith


lemma norm_sL_ge (t : ℝ) : 1 / 2 ≤ ‖sL t‖ ∧ |t| ≤ ‖sL t‖ := by
  constructor
  · have h := Complex.abs_re_le_norm (sL t)
    rw [sL_re] at h; norm_num at h; linarith
  · have h := Complex.abs_im_le_norm (sL t)
    simpa [sL] using h

lemma norm_d_ge (t : ℝ) : |t| ^ 3 ≤ ‖sL t‖ * ‖sL t + 1‖ * ‖sL t + 2‖ :=
  (perron_left_denominator_bounds t).2

/-- pointwise majorant for the smoothed left-line integrand -/
lemma pointwise_major (y h T : ℝ) (hy : 0 < y) (hh : 0 < h) (hT : 0 < T) (t : ℝ) :
    ‖(quadraticKernel (y + 2 * h) (sL t) - 2 * quadraticKernel (y + h) (sL t) +
      quadraticKernel y (sL t)) * logDeriv riemannZeta (sL t)‖ / h ^ 2 ≤
      (130 * y ^ (-(1 / 2 : ℝ)) + 8 * (1 + 32 / T) * (y + 2 * h) ^ (3 / 2 : ℝ) / (h ^ 2 * T ^ 2)) *
        (1 + (t / T) ^ 2)⁻¹ := by
  have hL : ‖logDeriv riemannZeta (sL t)‖ ≤ |t| + 32 := RvM.norm_logDeriv_zeta_left t
  have hh2 : 0 < h ^ 2 := by positivity
  have hq : 0 < 1 + (t / T) ^ 2 := by positivity
  have hA : 0 ≤ 130 * y ^ (-(1 / 2 : ℝ)) := by positivity
  have hB : 0 ≤ 8 * (1 + 32 / T) * (y + 2 * h) ^ (3 / 2 : ℝ) / (h ^ 2 * T ^ 2) := by positivity
  rw [norm_mul, div_le_iff₀ hh2]
  obtain ⟨hs1, hs2⟩ := norm_sL_ge t
  have hs0 : 0 < ‖sL t‖ := by linarith
  rcases le_or_gt |t| T with htT | htT
  · -- low region
    have hlow := secdiff_low y h hy hh t
    have hq2 : 1 + (t / T) ^ 2 ≤ 2 := by
      have : (t / T) ^ 2 ≤ 1 := by
        rw [div_pow, div_le_one (by positivity), ← sq_abs t]
        exact pow_le_pow_left₀ (abs_nonneg t) htT 2
      linarith
    have hratio : (|t| + 32) / ‖sL t‖ ≤ 65 := by
      rw [div_le_iff₀ hs0]; linarith
    have key : ‖quadraticKernel (y + 2 * h) (sL t) - 2 * quadraticKernel (y + h) (sL t) +
        quadraticKernel y (sL t)‖ * ‖logDeriv riemannZeta (sL t)‖ ≤
        h ^ 2 * (65 * y ^ (-(1 / 2 : ℝ))) := by
      calc _ ≤ h ^ 2 * (y ^ (-(1 / 2 : ℝ)) / ‖sL t‖) * (|t| + 32) := by
            gcongr
        _ = h ^ 2 * y ^ (-(1 / 2 : ℝ)) * ((|t| + 32) / ‖sL t‖) := by ring
        _ ≤ h ^ 2 * y ^ (-(1 / 2 : ℝ)) * 65 := by gcongr
        _ = _ := by ring
    have hqi : 1 / 2 ≤ (1 + (t / T) ^ 2)⁻¹ := by
      rw [inv_eq_one_div]; exact one_div_le_one_div_of_le hq hq2
    have hBq : 0 ≤ 8 * (1 + 32 / T) * (y + 2 * h) ^ (3 / 2 : ℝ) / (h ^ 2 * T ^ 2) *
        (1 + (t / T) ^ 2)⁻¹ := mul_nonneg hB (inv_nonneg.mpr hq.le)
    have hAq := mul_le_mul_of_nonneg_left hqi hA
    calc _ ≤ h ^ 2 * (65 * y ^ (-(1 / 2 : ℝ))) := key
      _ = h ^ 2 * (130 * y ^ (-(1 / 2 : ℝ)) * (1 / 2)) := by ring
      _ ≤ h ^ 2 * (130 * y ^ (-(1 / 2 : ℝ)) * (1 + (t / T) ^ 2)⁻¹ +
          8 * (1 + 32 / T) * (y + 2 * h) ^ (3 / 2 : ℝ) / (h ^ 2 * T ^ 2) * (1 + (t / T) ^ 2)⁻¹) := by
          gcongr; linarith
      _ = _ := by ring
  · -- high region
    have hhigh := secdiff_high y h hy hh t
    have hd := norm_d_ge t
    have ht0 : 0 < |t| := lt_trans hT htT
    have hd0 : 0 < |t| ^ 3 := pow_pos ht0 3
    set Y := (y + 2 * h) ^ (3 / 2 : ℝ)
    have hY : 0 ≤ Y := by positivity
    have key : ‖quadraticKernel (y + 2 * h) (sL t) - 2 * quadraticKernel (y + h) (sL t) +
        quadraticKernel y (sL t)‖ * ‖logDeriv riemannZeta (sL t)‖ ≤
        4 * (1 + 32 / T) * Y / t ^ 2 := by
      have h1 : ‖quadraticKernel (y + 2 * h) (sL t) - 2 * quadraticKernel (y + h) (sL t) +
          quadraticKernel y (sL t)‖ ≤ 4 * Y / |t| ^ 3 :=
        hhigh.trans (div_le_div_of_nonneg_left (by positivity) hd0 hd)
      have h2 : (|t| + 32) / |t| ^ 3 ≤ (1 + 32 / T) / t ^ 2 := by
        rw [div_le_div_iff₀ hd0 (by rw [← sq_abs]; exact pow_pos ht0 2), ← sq_abs t]
        have h3 : 32 * |t| ^ 2 ≤ 32 / T * |t| ^ 3 := by
          rw [div_mul_eq_mul_div, le_div_iff₀ hT]
          have := pow_pos ht0 2
          have e : 32 * |t| ^ 3 = 32 * |t| ^ 2 * |t| := by ring
          rw [e]
          exact mul_le_mul_of_nonneg_left htT.le (by positivity)
        nlinarith
      calc _ ≤ 4 * Y / |t| ^ 3 * (|t| + 32) := by gcongr
        _ = 4 * Y * ((|t| + 32) / |t| ^ 3) := by ring
        _ ≤ 4 * Y * ((1 + 32 / T) / t ^ 2) := by gcongr
        _ = _ := by ring
    have hq2 : 1 + (t / T) ^ 2 ≤ 2 * (t / T) ^ 2 := by
      have : 1 ≤ (t / T) ^ 2 := by
        rw [div_pow, le_div_iff₀ (by positivity), one_mul, ← sq_abs t]
        exact pow_le_pow_left₀ hT.le htT.le 2
      linarith
    have ht2 : 0 < t ^ 2 := by rw [← sq_abs]; positivity
    have hTq : T ^ 2 * (1 + (t / T) ^ 2) ≤ 2 * t ^ 2 := by
      have e : T ^ 2 * (1 + (t / T) ^ 2) = T ^ 2 + t ^ 2 := by field_simp
      rw [e]
      have : T ^ 2 ≤ t ^ 2 := by rw [← sq_abs t]; exact pow_le_pow_left₀ hT.le htT.le 2
      linarith
    have hAq : 0 ≤ 130 * y ^ (-(1 / 2 : ℝ)) * (1 + (t / T) ^ 2)⁻¹ :=
      mul_nonneg hA (inv_nonneg.mpr hq.le)
    have hc : 0 ≤ 8 * (1 + 32 / T) * Y := by positivity
    have e2 : 8 * (1 + 32 / T) * Y / (h ^ 2 * T ^ 2) * (1 + (t / T) ^ 2)⁻¹ * h ^ 2 =
        8 * (1 + 32 / T) * Y / (T ^ 2 * (1 + (t / T) ^ 2)) := by field_simp
    have e3 : 4 * (1 + 32 / T) * Y / t ^ 2 = 8 * (1 + 32 / T) * Y / (2 * t ^ 2) := by
      field_simp; ring
    have hmain : 4 * (1 + 32 / T) * Y / t ^ 2 ≤
        8 * (1 + 32 / T) * Y / (h ^ 2 * T ^ 2) * (1 + (t / T) ^ 2)⁻¹ * h ^ 2 := by
      rw [e2, e3]
      exact div_le_div_of_nonneg_left hc (by positivity) hTq
    calc _ ≤ 4 * (1 + 32 / T) * Y / t ^ 2 := key
      _ ≤ 8 * (1 + 32 / T) * Y / (h ^ 2 * T ^ 2) * (1 + (t / T) ^ 2)⁻¹ * h ^ 2 := hmain
      _ ≤ _ := by
          have := mul_nonneg hAq hh2.le
          nlinarith


theorem remainder_bound (y h T : ℝ) (hy : 0 < y) (hh : 0 < h) (hT : 0 < T) :
    ‖(perronLeftRemainder (y + 2 * h) - 2 * perronLeftRemainder (y + h) +
        perronLeftRemainder y) / (h : ℂ) ^ 2‖ ≤
      65 * T * y ^ (-(1 / 2 : ℝ)) + 4 * (1 + 32 / T) * (y + 2 * h) ^ (3 / 2 : ℝ) / (h ^ 2 * T) := by
  have i2 := perron_left_vertical_integrable (y + 2 * h) (by linarith)
  have i1 := perron_left_vertical_integrable (y + h) (by linarith)
  have i0 := perron_left_vertical_integrable y hy
  set G : ℝ → ℂ := fun t => perronIntegrand (y + 2 * h) (-(1 / 2 : ℂ) + t * I) -
    2 * perronIntegrand (y + h) (-(1 / 2 : ℂ) + t * I) + perronIntegrand y (-(1 / 2 : ℂ) + t * I)
    with hG
  have hcomb : perronLeftRemainder (y + 2 * h) - 2 * perronLeftRemainder (y + h) +
      perronLeftRemainder y = (1 / (2 * Real.pi) : ℂ) * ∫ t, G t := by
    unfold perronLeftRemainder
    have h1 : Integrable (fun t : ℝ => perronIntegrand (y + 2 * h) (-(1 / 2 : ℂ) + t * I) -
        2 * perronIntegrand (y + h) (-(1 / 2 : ℂ) + t * I)) := i2.sub (i1.const_mul 2)
    have e1 := integral_add h1 i0
    have e2 := integral_sub i2 (i1.const_mul 2)
    have e3 := integral_const_mul (μ := volume) (2 : ℂ)
      (fun t : ℝ => perronIntegrand (y + h) (-(1 / 2 : ℂ) + t * I))
    rw [hG, e1, e2, e3]
    ring
  have hGeq : ∀ t, G t = -((quadraticKernel (y + 2 * h) (sL t) - 2 * quadraticKernel (y + h) (sL t) +
      quadraticKernel y (sL t)) * logDeriv riemannZeta (sL t)) := by
    intro t; simp only [hG, perronIntegrand, sL]; ring
  set c : ℝ := 130 * y ^ (-(1 / 2 : ℝ)) + 8 * (1 + 32 / T) * (y + 2 * h) ^ (3 / 2 : ℝ) / (h ^ 2 * T ^ 2)
  have hmaj : Integrable (fun t : ℝ => c * (1 + (t / T) ^ 2)⁻¹) :=
    (integrable_inv_one_add_sq.comp_div hT.ne').const_mul c
  have hint : ∫ t : ℝ, c * (1 + (t / T) ^ 2)⁻¹ = c * (T * Real.pi) := by
    rw [integral_const_mul]
    congr 1
    have := Measure.integral_comp_div (fun t : ℝ => (1 + t ^ 2)⁻¹) T
    rw [this, integral_univ_inv_one_add_sq, abs_of_pos hT, smul_eq_mul]
  have hh2 : 0 < h ^ 2 := by positivity
  have hpt : ∀ t, ‖G t‖ / h ^ 2 ≤ c * (1 + (t / T) ^ 2)⁻¹ := by
    intro t
    rw [hGeq, norm_neg]
    exact pointwise_major y h T hy hh hT t
  have hle : ∫ t, ‖G t‖ / h ^ 2 ≤ c * (T * Real.pi) := by
    rw [← hint]
    exact integral_mono_of_nonneg (Filter.Eventually.of_forall (fun t => by positivity)) hmaj
      (Filter.Eventually.of_forall hpt)
  rw [hcomb, norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh]
  have hn : ‖(1 / (2 * Real.pi) : ℂ)‖ = 1 / (2 * Real.pi) := by
    rw [show (1 / (2 * Real.pi) : ℂ) = ((1 / (2 * Real.pi) : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [hn]
  have hnorm := norm_integral_le_integral_norm (μ := volume) G
  rw [integral_div] at hle
  have hπ : 0 < Real.pi := Real.pi_pos
  calc 1 / (2 * Real.pi) * ‖∫ t, G t‖ / h ^ 2 ≤ 1 / (2 * Real.pi) * ((∫ t, ‖G t‖) / h ^ 2) := by
        rw [mul_div_assoc]; gcongr
    _ ≤ 1 / (2 * Real.pi) * (c * (T * Real.pi)) := by gcongr
    _ = _ := by
        simp only [c]
        field_simp
        ring

end SchoenfeldR

end

-- ===== M1 =====
section

open DusartSmoothing Complex MeasureTheory SchoenfeldAbel

namespace SchoenfeldM

lemma dba_le (f : ℝ → ℝ) (hf : Monotone f) (y h : ℝ) (hh : 0 < h) :
    f y ≤ doubleBoxAverage f y h ∧ doubleBoxAverage f y h ≤ f (y + 2 * h) := by
  have hg := boxAverage_mono f hf h hh
  have b1 := boxAverage_bounds (fun z => boxAverage f z h) hg y h hh
  have b2 := boxAverage_bounds f hf y h hh
  have b3 := boxAverage_bounds f hf (y + h) h hh
  unfold doubleBoxAverage
  refine ⟨b2.1.trans b1.1, b1.2.trans ?_⟩
  have : y + h + h = y + 2 * h := by ring
  rw [this] at b3
  exact b3.2

/-- the explicit-formula error for one double box average -/
lemma dba_error (hRH : ∀ ρ : ℂ, RvM.IsNontrivialZero ρ → ρ.re = 1 / 2)
    (hlow : ∀ t : ℝ, 14 ≤ t → t ≤ 2500 → (RvM.Ncount 4 t : ℝ) ≤ RvM.countingMain t + 5 / 2)
    (h14 : ∀ ρ : ℂ, RvM.IsNontrivialZero ρ → 0 < ρ.im → 14 ≤ ρ.im)
    (y h X : ℝ) (hy : 1 ≤ y) (hh : 0 < h) (hX : y + 2 * h ≤ X) (hθ : 14 ≤ 2 * X / h) :
    |doubleBoxAverage Chebyshev.psi y h - (y + h) + Real.log (2 * Real.pi)| ≤
      Real.sqrt X * (2 * (Gθ (2 * X / h) + 1 / 100)) +
        (65 * (X / h) * y ^ (-(1 / 2 : ℝ)) +
          4 * (1 + 32 / (X / h)) * X ^ (3 / 2 : ℝ) / (h ^ 2 * (X / h))) := by
  obtain ⟨N, hN⟩ := exists_nat_ge (y + 2 * h)
  have hEF := doubleBoxAverage_psi_explicit_formula N y h hy hh hN
  rw [logDeriv_zeta_zero] at hEF
  set Sz := ∑' ρ : NontrivialZetaZero, (RvM.zeroMult ρ.val : ℂ) * smoothedZeroKernel y h ρ.val
  set R := (perronLeftRemainder (y + 2 * h) - 2 * perronLeftRemainder (y + h) +
        perronLeftRemainder y) / (h : ℂ) ^ 2
  have hZ := zero_series_bound hRH hlow h14 y h X hy hh hX hθ
  have hT : 0 < X / h := by
    apply div_pos _ hh; linarith
  have hR := SchoenfeldR.remainder_bound y h (X / h) (by linarith) hh hT
  have hR' : ‖R‖ ≤ 65 * (X / h) * y ^ (-(1 / 2 : ℝ)) +
      4 * (1 + 32 / (X / h)) * X ^ (3 / 2 : ℝ) / (h ^ 2 * (X / h)) := by
    refine hR.trans ?_
    gcongr
  have hc : ((doubleBoxAverage Chebyshev.psi y h - (y + h) + Real.log (2 * Real.pi) : ℝ) : ℂ) =
      -Sz + R := by
    push_cast
    rw [hEF]
    push_cast
    ring
  have hn : |doubleBoxAverage Chebyshev.psi y h - (y + h) + Real.log (2 * Real.pi)| = ‖-Sz + R‖ := by
    rw [← hc, Complex.norm_real, Real.norm_eq_abs]
  rw [hn]
  calc ‖-Sz + R‖ ≤ ‖Sz‖ + ‖R‖ := by
        calc _ ≤ ‖-Sz‖ + ‖R‖ := norm_add_le _ _
          _ = _ := by rw [norm_neg]
    _ ≤ _ := add_le_add hZ hR'

/-- the pointwise ψ bound -/
theorem psi_error (hRH : ∀ ρ : ℂ, RvM.IsNontrivialZero ρ → ρ.re = 1 / 2)
    (hlow : ∀ t : ℝ, 14 ≤ t → t ≤ 2500 → (RvM.Ncount 4 t : ℝ) ≤ RvM.countingMain t + 5 / 2)
    (h14 : ∀ ρ : ℂ, RvM.IsNontrivialZero ρ → 0 < ρ.im → 14 ≤ ρ.im)
    (x h : ℝ) (hh : 0 < h) (hx : 1 ≤ x - 2 * h) (hθ : 14 ≤ 2 * (x + 2 * h) / h) :
    |Chebyshev.psi x - x| ≤ h + Real.log (2 * Real.pi) +
      Real.sqrt (x + 2 * h) * (2 * (Gθ (2 * (x + 2 * h) / h) + 1 / 100)) +
        (65 * ((x + 2 * h) / h) * (x - 2 * h) ^ (-(1 / 2 : ℝ)) +
          4 * (1 + 32 / ((x + 2 * h) / h)) * (x + 2 * h) ^ (3 / 2 : ℝ) /
            (h ^ 2 * ((x + 2 * h) / h))) := by
  have hmono : Monotone Chebyshev.psi := Chebyshev.psi_mono
  have hl2 : 0 < Real.log (2 * Real.pi) := Real.log_pos (by linarith [Real.pi_gt_three])
  -- upper
  have e1 := dba_error hRH hlow h14 x h (x + 2 * h) (by linarith) hh le_rfl hθ
  have u1 := (dba_le Chebyshev.psi hmono x h hh).1
  -- lower
  have e2 := dba_error hRH hlow h14 (x - 2 * h) h (x + 2 * h) hx hh (by linarith) hθ
  have u2 := (dba_le Chebyshev.psi hmono (x - 2 * h) h hh).2
  rw [show x - 2 * h + 2 * h = x by ring] at u2
  have hy : (x : ℝ) ^ (-(1 / 2 : ℝ)) ≤ (x - 2 * h) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by norm_num)
  have hT : 0 ≤ (x + 2 * h) / h := by apply div_nonneg _ hh.le; linarith
  have hmul : 65 * ((x + 2 * h) / h) * x ^ (-(1 / 2 : ℝ)) ≤
      65 * ((x + 2 * h) / h) * (x - 2 * h) ^ (-(1 / 2 : ℝ)) := by gcongr
  rw [abs_le] at e1 e2 ⊢
  constructor
  · linarith [e2.1, e2.2]
  · linarith [e1.1, e1.2]

end SchoenfeldM

end

-- ===== N0 =====
section

open Real

namespace SchoenfeldN

lemma exp_one_le : exp 1 ≤ 2.7182818286 := exp_one_lt_d9.le
lemma exp_one_ge : 2.7182818283 ≤ exp 1 := exp_one_gt_d9.le

lemma exp_062 : exp 0.62 ≤ 1.859 := by
  have h := Real.exp_bound' (x := 0.62) (by norm_num) (by norm_num) (n := 8) (by norm_num)
  refine h.trans ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

lemma exp_069 : exp 0.69 ≤ 1.9938 := by
  have h := Real.exp_bound' (x := 0.69) (by norm_num) (by norm_num) (n := 8) (by norm_num)
  refine h.trans ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

lemma exp_162 : exp 1.62 ≤ 5.054 := by
  have : exp 1.62 = exp 1 * exp 0.62 := by rw [← Real.exp_add]; norm_num
  rw [this]
  have := mul_le_mul exp_one_le exp_062 (exp_pos _).le (by norm_num)
  linarith

lemma exp_169 : exp 1.69 ≤ 5.42 := by
  have : exp 1.69 = exp 1 * exp 0.69 := by rw [← Real.exp_add]; norm_num
  rw [this]
  have := mul_le_mul exp_one_le exp_069 (exp_pos _).le (by norm_num)
  linarith

lemma exp_nat_eq (n : ℕ) : exp n = exp 1 ^ n := by
  rw [← Real.exp_nat_mul]; simp

lemma exp_13_ge : 442000 ≤ exp 13 := by
  have h : exp 13 = exp 1 ^ 13 := by exact_mod_cast exp_nat_eq 13
  rw [h]
  calc (442000 : ℝ) ≤ 2.7182818283 ^ 13 := by norm_num
    _ ≤ exp 1 ^ 13 := pow_le_pow_left₀ (by norm_num) exp_one_ge 13

lemma exp_7_ge : 1096 ≤ exp 7 := by
  have h : exp 7 = exp 1 ^ 7 := by exact_mod_cast exp_nat_eq 7
  rw [h]
  calc (1096 : ℝ) ≤ 2.7182818283 ^ 7 := by norm_num
    _ ≤ exp 1 ^ 7 := pow_le_pow_left₀ (by norm_num) exp_one_ge 7

lemma exp_7_le : exp 7 ≤ 1097 := by
  have h : exp 7 = exp 1 ^ 7 := by exact_mod_cast exp_nat_eq 7
  rw [h]
  calc exp 1 ^ 7 ≤ 2.7182818286 ^ 7 := pow_le_pow_left₀ (exp_pos 1).le exp_one_le 7
    _ ≤ 1097 := by norm_num

lemma exp_65_ge : 664 ≤ exp 6.5 := by
  have h : exp 6.5 * exp 6.5 = exp 13 := by rw [← Real.exp_add]; norm_num
  have h1 := exp_13_ge
  nlinarith [exp_pos 6.5]

lemma log_two_pi_lt : log (2 * π) < 2 := by
  rw [Real.log_lt_iff_lt_exp (by positivity)]
  have h : exp 2 = exp 1 ^ 2 := by exact_mod_cast exp_nat_eq 2
  rw [h]
  nlinarith [pi_lt_d2, exp_one_ge]

/-- exp d ≥ (1 + d/3)^3 for d ≥ 0 -/
lemma exp_ge_cube (d : ℝ) (hd : 0 ≤ d) : (1 + d / 3) ^ 3 ≤ exp d := by
  have h : exp d = exp (d / 3) ^ 3 := by rw [← Real.exp_nat_mul]; norm_num; ring_nf
  rw [h]
  have := Real.add_one_le_exp (d / 3)
  exact pow_le_pow_left₀ (by linarith) (by linarith) 3

end SchoenfeldN

end

-- ===== N1 =====
section

open Real SchoenfeldAbel DusartSmoothing

namespace SchoenfeldN

noncomputable def P (w : ℝ) : ℝ := (w ^ 2 + w - 1 / 2) / (4 * π)

lemma F1_nonneg (t : ℝ) : 0 ≤ F1 t := by unfold F1; have := pi_pos; positivity

lemma GA_eq (θ : ℝ) : GA θ = P (log (θ / (2 * π))) - F1 14 + 5 / 28 + θ ^ 2 / 10 ^ 8 := by
  unfold GA P F1; field_simp; ring

lemma GB_eq (θ : ℝ) : GB θ = P (log (θ / (2 * π))) - F1 14 + 5 / 28 + 638 / 10000 +
    (9 * log θ + 83) / θ := by
  unfold GB P F1; field_simp; ring

lemma P_mono {w v : ℝ} (hw : 0 ≤ w) (hwv : w ≤ v) : P w ≤ P v := by
  unfold P
  apply div_le_div_of_nonneg_right _ (by have := pi_pos; positivity)
  nlinarith

lemma G_le_A {θ : ℝ} (h0 : 0 ≤ θ) (h2 : θ ≤ 1360) :
    Gθ θ + 1 / 100 ≤ P (log (θ / (2 * π))) + (5 / 28 + 1 / 100 + 185 / 10000) := by
  have hθ : θ ≤ 2500 := by linarith
  unfold Gθ; rw [if_pos hθ, GA_eq]
  have := F1_nonneg 14
  have : θ ^ 2 ≤ 1360 ^ 2 := pow_le_pow_left₀ h0 h2 2
  linarith

lemma rational_log_bound {θ : ℝ} (hθ : 2500 ≤ θ) : (9 * log θ + 83) / θ ≤ 625 / 10000 := by
  have hp : 0 < θ := by linarith
  have h1 := Real.log_le_sub_one_of_pos (show 0 < θ / 2500 by positivity)
  rw [Real.log_div hp.ne' (by norm_num)] at h1
  have h2 := log_2500_lt
  rw [div_le_iff₀ hp]
  linarith

lemma G_le_B {θ : ℝ} (h0 : 0 ≤ θ) :
    Gθ θ + 1 / 100 ≤ P (log (θ / (2 * π))) + (5 / 28 + 1 / 100 + 638 / 10000 + 625 / 10000) := by
  have := F1_nonneg 14
  unfold Gθ
  split_ifs with hθ
  · rw [GA_eq]
    have : θ ^ 2 ≤ 2500 ^ 2 := pow_le_pow_left₀ h0 hθ 2
    linarith
  · rw [GB_eq]
    have := rational_log_bound (le_of_lt (not_le.1 hθ))
    linarith

/-- log (θ/2π) ≤ a - m when θ = 8 s/a + 4 and s = exp a -/
lemma w_le {a s m c : ℝ} (ha : 0 < a) (hs : s = exp a) (hm : exp m ≤ c)
    (hineq : (8 * s + 4 * a) * c ≤ 2 * π * s * a) :
    log ((8 * s / a + 4) / (2 * π)) ≤ a - m := by
  have hsp : 0 < s := by rw [hs]; exact exp_pos a
  have hπ := pi_pos
  rw [Real.log_le_iff_le_exp (by positivity), Real.exp_sub, ← hs,
    div_le_div_iff₀ (by positivity) (exp_pos m)]
  have e : (8 * s / a + 4) = (8 * s + 4 * a) / a := by field_simp
  rw [e, div_mul_eq_mul_div, div_le_iff₀ ha]
  have : (8 * s + 4 * a) * exp m ≤ (8 * s + 4 * a) * c :=
    mul_le_mul_of_nonneg_left hm (by positivity)
  linarith

lemma w_nonneg {a s : ℝ} (ha : 0 < a) (hsa : 90 * a ≤ s) :
    0 ≤ log ((8 * s / a + 4) / (2 * π)) := by
  apply Real.log_nonneg
  have hπ := pi_lt_d2
  rw [le_div_iff₀ (by positivity), one_mul]
  have : 90 ≤ s / a := by rw [le_div_iff₀ ha]; linarith
  have : 8 * s / a = 8 * (s / a) := by ring
  linarith

/-- the analytic bound evaluated at h = √x log x / 8 -/
theorem final_bound (hRH : ∀ ρ : ℂ, RvM.IsNontrivialZero ρ → ρ.re = 1 / 2)
    (hlow : ∀ t : ℝ, 14 ≤ t → t ≤ 2500 → (RvM.Ncount 4 t : ℝ) ≤ RvM.countingMain t + 5 / 2)
    (h14 : ∀ ρ : ℂ, RvM.IsNontrivialZero ρ → 0 < ρ.im → 14 ≤ ρ.im)
    (x a s B : ℝ) (ha : 6.5 ≤ a) (hs : 664 ≤ s) (hsa : 90 * a ≤ s)
    (hxs : x = s ^ 2) (hsq : Real.sqrt x = s) (hlog : Real.log x = 2 * a)
    (hB0 : 0 ≤ B) (hG : Gθ (8 * s / a + 4) + 1 / 100 ≤ B)
    (hkey : s * a / 4 + 46 + (s + a / 4) * (2 * B) < s * (2 * a) ^ 2 / (8 * π)) :
    |Chebyshev.psi x - x| < Real.sqrt x * (Real.log x) ^ 2 / (8 * Real.pi) := by
  have ha0 : 0 < a := by linarith
  have hs0 : 0 < s := by linarith
  set h := s * a / 4 with hh
  have hh0 : 0 < h := by positivity
  have hX : x + 2 * h = s ^ 2 + s * a / 2 := by rw [hxs, hh]; ring
  have hY : x - 2 * h = s ^ 2 - s * a / 2 := by rw [hxs, hh]; ring
  have hYlow : (99 / 100 * s) ^ 2 ≤ x - 2 * h := by rw [hY]; nlinarith
  have hx1 : 1 ≤ x - 2 * h := by nlinarith
  have hθ : 2 * (x + 2 * h) / h = 8 * s / a + 4 := by
    rw [hX, hh]; field_simp; ring
  have hT : (x + 2 * h) / h = 4 * s / a + 2 := by
    rw [hX, hh]; field_simp; ring
  have hsa' : 90 ≤ s / a := by rw [le_div_iff₀ ha0]; linarith
  have hθ14 : 14 ≤ 2 * (x + 2 * h) / h := by
    rw [hθ]; have : 8 * s / a = 8 * (s / a) := by ring
    linarith
  have hE := SchoenfeldM.psi_error hRH hlow h14 x h hh0 hx1 hθ14
  rw [hθ] at hE
  -- square roots
  have hXp : 0 < x + 2 * h := by rw [hX]; positivity
  have hsqX : Real.sqrt (x + 2 * h) ≤ s + a / 4 := by
    rw [show s + a / 4 = Real.sqrt ((s + a / 4) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
    apply Real.sqrt_le_sqrt; rw [hX]; nlinarith
  have hsqY : 99 / 100 * s ≤ Real.sqrt (x - 2 * h) := by
    rw [show 99 / 100 * s = Real.sqrt ((99 / 100 * s) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
    exact Real.sqrt_le_sqrt hYlow
  have hYr : (x - 2 * h) ^ (-(1 / 2 : ℝ)) = (Real.sqrt (x - 2 * h))⁻¹ := by
    rw [Real.rpow_neg (by linarith), Real.sqrt_eq_rpow]
  have hXr : (x + 2 * h) ^ (3 / 2 : ℝ) = (x + 2 * h) * Real.sqrt (x + 2 * h) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hXp, Real.rpow_one,
      Real.sqrt_eq_rpow]
  -- E2
  have hE2 : 65 * ((x + 2 * h) / h) * (x - 2 * h) ^ (-(1 / 2 : ℝ)) ≤ 41 := by
    rw [hYr, hT]
    have hq : 0 < Real.sqrt (x - 2 * h) := by linarith
    rw [← div_eq_mul_inv, div_le_iff₀ hq]
    have e : 4 * s / a = 4 * (s / a) := by ring
    have h1 : s / a ≤ s / (13 / 2) := div_le_div_of_nonneg_left hs0.le (by norm_num) (by norm_num at ha ⊢; linarith)
    rw [e]
    linarith
  -- E3
  have hE3 : 4 * (1 + 32 / ((x + 2 * h) / h)) * (x + 2 * h) ^ (3 / 2 : ℝ) /
      (h ^ 2 * ((x + 2 * h) / h)) ≤ 3 := by
    rw [hXr]
    have e : 4 * (1 + 32 / ((x + 2 * h) / h)) * ((x + 2 * h) * Real.sqrt (x + 2 * h)) /
        (h ^ 2 * ((x + 2 * h) / h)) = 4 * (1 + 32 / ((x + 2 * h) / h)) * Real.sqrt (x + 2 * h) / h := by
      field_simp
    rw [e, hT, div_le_iff₀ hh0]
    have hT400 : 32 / (4 * s / a + 2) ≤ 9 / 100 := by
      rw [div_le_iff₀ (by positivity)]
      have : 4 * s / a = 4 * (s / a) := by ring
      linarith
    have hsq0 : 0 ≤ Real.sqrt (x + 2 * h) := Real.sqrt_nonneg _
    have := mul_le_mul (show 4 * (1 + 32 / (4 * s / a + 2)) ≤ 4 * (1 + 9 / 100) by linarith)
      hsqX hsq0 (by norm_num)
    rw [hh]
    nlinarith
  -- G term
  have hGt : Real.sqrt (x + 2 * h) * (2 * (Gθ (8 * s / a + 4) + 1 / 100)) ≤ (s + a / 4) * (2 * B) := by
    calc _ ≤ Real.sqrt (x + 2 * h) * (2 * B) :=
          mul_le_mul_of_nonneg_left (by linarith) (Real.sqrt_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_right hsqX (by linarith)
  have hl2 := log_two_pi_lt
  rw [hsq, hlog]
  have := abs_nonneg (Chebyshev.psi x - x)
  linarith

end SchoenfeldN

end

-- ===== N2 =====
section

open Real SchoenfeldAbel DusartSmoothing

namespace SchoenfeldN

lemma pi_lo : (3141592 / 1000000 : ℝ) < π := by have := pi_gt_d6; norm_num at this ⊢; linarith
lemma pi_hi : π < (31416 / 10000 : ℝ) := by have := pi_lt_d4; norm_num at this ⊢; linarith

/-- reduction of the key inequality to a polynomial one -/
lemma key_of_poly (a s m K : ℝ) (hs : 0 < s)
    (hp : 2 * π * (s * a / 4 + 46) + (s + a / 4) * (((a - m) ^ 2 + (a - m) - 1 / 2) + 4 * π * K)
      < s * a ^ 2) :
    s * a / 4 + 46 + (s + a / 4) * (2 * (P (a - m) + K)) < s * (2 * a) ^ 2 / (8 * π) := by
  have hπ := pi_pos
  have e1 : s * a / 4 + 46 + (s + a / 4) * (2 * (P (a - m) + K)) =
      (2 * π * (s * a / 4 + 46) + (s + a / 4) * (((a - m) ^ 2 + (a - m) - 1 / 2) + 4 * π * K)) /
        (2 * π) := by
    unfold P; field_simp; ring
  have e2 : s * (2 * a) ^ 2 / (8 * π) = s * a ^ 2 / (2 * π) := by field_simp; ring
  rw [e1, e2]
  exact div_lt_div_of_pos_right hp (by positivity)

lemma poly_A (a s : ℝ) (ha : 13 / 2 ≤ a) (ha7 : a ≤ 7) (hs : 664 ≤ s) :
    2 * π * (s * a / 4 + 46) + (s + a / 4) * (((a - 81 / 50) ^ 2 + (a - 81 / 50) - 1 / 2) +
      4 * π * (5 / 28 + 1 / 100 + 185 / 10000)) < s * a ^ 2 := by
  have h1 := pi_lo
  have h2 := pi_hi
  set b := a ^ 2 - π * a / 2 - ((a - 81 / 50) ^ 2 + (a - 81 / 50) - 1 / 2) -
    4 * π * (5 / 28 + 1 / 100 + 185 / 10000) with hb
  have hb1 : 124 / 100 ≤ b := by
    rw [hb]; nlinarith [mul_nonneg (sub_nonneg.2 h2.le) (show (0 : ℝ) ≤ a by linarith)]
  have hsb : 664 * (124 / 100) ≤ s * b := mul_le_mul hs hb1 (by norm_num) (by linarith)
  set Q := (a - 81 / 50) ^ 2 + (a - 81 / 50) - 1 / 2 with hQ
  have hQ1 : Q ≤ 339 / 10 := by rw [hQ]; nlinarith
  have hQ0 : 0 ≤ Q := by rw [hQ]; nlinarith
  have hK : 4 * π * (5 / 28 + 1 / 100 + 185 / 10000) ≤ 261 / 100 := by nlinarith
  have hc : a / 4 * (Q + 4 * π * (5 / 28 + 1 / 100 + 185 / 10000)) ≤ 7 / 4 * (339 / 10 + 261 / 100) :=
    mul_le_mul (by linarith) (by linarith) (by positivity) (by norm_num)
  have e : 2 * π * (s * a / 4 + 46) + (s + a / 4) * (Q + 4 * π * (5 / 28 + 1 / 100 + 185 / 10000)) =
      s * a ^ 2 - s * b + 92 * π + a / 4 * (Q + 4 * π * (5 / 28 + 1 / 100 + 185 / 10000)) := by
    rw [hb, hQ]; ring
  rw [e]
  nlinarith

lemma poly_B (a s : ℝ) (ha : 7 ≤ a) (hs : 1096 * (1 + (a - 7) / 3) ^ 3 ≤ s) :
    2 * π * (s * a / 4 + 46) + (s + a / 4) * (((a - 169 / 100) ^ 2 + (a - 169 / 100) - 1 / 2) +
      4 * π * (5 / 28 + 1 / 100 + 638 / 10000 + 625 / 10000)) < s * a ^ 2 := by
  have h1 := pi_lo
  have h2 := pi_hi
  set d := a - 7 with hd
  have hd0 : 0 ≤ d := by linarith
  have ha' : a = 7 + d := by linarith
  set b := a ^ 2 - π * a / 2 - ((a - 169 / 100) ^ 2 + (a - 169 / 100) - 1 / 2) -
    4 * π * (5 / 28 + 1 / 100 + 638 / 10000 + 625 / 10000) with hb
  have hb1 : 809 / 1000 * a - 463 / 100 ≤ b := by
    rw [hb]; nlinarith [mul_nonneg (sub_nonneg.2 h2.le) (show (0 : ℝ) ≤ a by linarith)]
  have hb0 : 0 ≤ 809 / 1000 * a - 463 / 100 := by linarith
  have hsb : 1096 * (1 + d / 3) ^ 3 * (809 / 1000 * a - 463 / 100) ≤ s * b :=
    mul_le_mul hs hb1 hb0 (by linarith [show 0 ≤ 1096 * (1 + d / 3) ^ 3 by positivity])
  set Q := (a - 169 / 100) ^ 2 + (a - 169 / 100) - 1 / 2 with hQ
  have hQ0 : 0 ≤ Q := by rw [hQ]; nlinarith
  have hK : 4 * π * (5 / 28 + 1 / 100 + 638 / 10000 + 625 / 10000) ≤ 396 / 100 := by nlinarith
  have hc : a / 4 * (Q + 4 * π * (5 / 28 + 1 / 100 + 638 / 10000 + 625 / 10000)) ≤
      a / 4 * (Q + 396 / 100) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have e : 2 * π * (s * a / 4 + 46) + (s + a / 4) *
      (Q + 4 * π * (5 / 28 + 1 / 100 + 638 / 10000 + 625 / 10000)) =
      s * a ^ 2 - s * b + 92 * π +
        a / 4 * (Q + 4 * π * (5 / 28 + 1 / 100 + 638 / 10000 + 625 / 10000)) := by
    rw [hb, hQ]; ring
  rw [e]
  have hpoly : a / 4 * (Q + 396 / 100) + 92 * (31416 / 10000) <
      1096 * (1 + d / 3) ^ 3 * (809 / 1000 * a - 463 / 100) := by
    rw [hQ, ha']
    nlinarith [pow_nonneg hd0 2, pow_nonneg hd0 3, pow_nonneg hd0 4]
  nlinarith

lemma B_nonneg (a m K : ℝ) (h : 1 ≤ a - m) (hK : 0 ≤ K) : 0 ≤ P (a - m) + K := by
  unfold P
  have := pi_pos
  exact add_nonneg (div_nonneg (by nlinarith) (by positivity)) hK

/-- **Schoenfeld's ψ bound for x ≥ e¹³**, from RH and the two low-height zero facts. -/
theorem psi_large (hRH : ∀ ρ : ℂ, RvM.IsNontrivialZero ρ → ρ.re = 1 / 2)
    (hlow : ∀ t : ℝ, 14 ≤ t → t ≤ 2500 → (RvM.Ncount 4 t : ℝ) ≤ RvM.countingMain t + 5 / 2)
    (h14 : ∀ ρ : ℂ, RvM.IsNontrivialZero ρ → 0 < ρ.im → 14 ≤ ρ.im)
    (x : ℝ) (hx : exp 13 ≤ x) :
    |Chebyshev.psi x - x| < Real.sqrt x * (Real.log x) ^ 2 / (8 * Real.pi) := by
  have hx0 : 0 < x := lt_of_lt_of_le (exp_pos 13) hx
  set a := Real.log x / 2 with ha_def
  have ha : 13 / 2 ≤ a := by
    have := Real.log_le_log (exp_pos 13) hx; rw [Real.log_exp] at this; linarith
  have hsa : Real.sqrt x = exp a := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx0, ha_def]; ring_nf
  set s := Real.sqrt x with hs_def
  have hxs : x = s ^ 2 := by rw [hs_def, Real.sq_sqrt hx0.le]
  have hlog : Real.log x = 2 * a := by rw [ha_def]; ring
  have hs664 : 664 ≤ s := by
    rw [hsa]; exact exp_65_ge.trans (exp_le_exp.2 (by norm_num at ha ⊢; linarith))
  have ha0 : 0 < a := by linarith
  have hs0 : 0 < s := by linarith
  have h1 := pi_lo
  rcases le_or_gt a 7 with ha7 | ha7
  · have hsle : s ≤ 1097 := by rw [hsa]; exact (exp_le_exp.2 ha7).trans exp_7_le
    have hs90 : 90 * a ≤ s := by linarith
    have hw0 := w_nonneg ha0 hs90
    have hw := w_le (m := 81 / 50) (c := 5054 / 1000) ha0 hsa
      (by have := exp_162; norm_num at this ⊢; exact this)
      (by nlinarith [mul_pos (sub_pos.2 h1) (mul_pos hs0 ha0),
            mul_nonneg (sub_nonneg.2 ha) hs0.le])
    have hθ0 : 0 ≤ 8 * s / a + 4 := by positivity
    have hθ1 : 8 * s / a + 4 ≤ 1360 := by
      have : s / a ≤ s / (13 / 2) := div_le_div_of_nonneg_left hs0.le (by norm_num) ha
      have e : 8 * s / a = 8 * (s / a) := by ring
      rw [e]; linarith
    have hG := (G_le_A hθ0 hθ1).trans
      (by linarith [P_mono hw0 hw] : _ ≤ P (a - 81 / 50) + (5 / 28 + 1 / 100 + 185 / 10000))
    exact final_bound hRH hlow h14 x a s _ (by norm_num at ha ⊢; linarith) hs664 hs90 hxs
      hs_def.symm hlog (B_nonneg _ _ _ (by linarith) (by norm_num)) hG
      (key_of_poly a s _ _ hs0 (poly_A a s ha ha7 hs664))
  · have hs7 : 1096 * (1 + (a - 7) / 3) ^ 3 ≤ s := by
      have e : exp a = exp 7 * exp (a - 7) := by rw [← Real.exp_add]; ring_nf
      rw [hsa, e]
      exact mul_le_mul exp_7_ge (exp_ge_cube _ (by linarith)) (by positivity) (exp_pos 7).le
    have hcube : 1 + (a - 7) ≤ (1 + (a - 7) / 3) ^ 3 := by
      nlinarith [pow_nonneg (show (0 : ℝ) ≤ a - 7 by linarith) 2,
        pow_nonneg (show (0 : ℝ) ≤ a - 7 by linarith) 3]
    have hs90 : 90 * a ≤ s := by nlinarith
    have hw0 := w_nonneg ha0 hs90
    have hw := w_le (m := 169 / 100) (c := 542 / 100) ha0 hsa
      (by have := exp_169; norm_num at this ⊢; exact this)
      (by nlinarith [mul_pos (sub_pos.2 h1) (mul_pos hs0 ha0),
            mul_nonneg (sub_nonneg.2 ha7.le) hs0.le])
    have hθ0 : 0 ≤ 8 * s / a + 4 := by positivity
    have hG := (G_le_B hθ0).trans
      (by linarith [P_mono hw0 hw] :
        _ ≤ P (a - 169 / 100) + (5 / 28 + 1 / 100 + 638 / 10000 + 625 / 10000))
    exact final_bound hRH hlow h14 x a s _ (by norm_num at ha ⊢; linarith) hs664 hs90 hxs
      hs_def.symm hlog (B_nonneg _ _ _ (by linarith) (by norm_num)) hG
      (key_of_poly a s _ _ hs0 (poly_B a s ha7.le hs7))

end SchoenfeldN

end


open DusartSmoothing in
theorem solution
    (hRH : ∀ s : ℂ, riemannZeta s = 0 → (¬∃ n : ℕ, s = -2 * (↑n + 1)) → s ≠ 1 → s.re = 1 / 2)
    (hlow : ∀ t : ℝ, 14 ≤ t → t ≤ 2500 →
      (DusartSmoothing.RvM.Ncount 0 t : ℝ) ≤
        t / (2 * Real.pi) * (Real.log (t / (2 * Real.pi)) - 1) + 5 / 2)
    (x : ℝ) (hx : Real.exp 13 ≤ x) :
    |Chebyshev.psi x - x| < Real.sqrt x * Real.log x ^ 2 / (8 * Real.pi) := by
  have hRH' : ∀ ρ : ℂ, RvM.IsNontrivialZero ρ → ρ.re = 1 / 2 := by
    intro ρ hρ
    apply hRH ρ hρ.1
    · rintro ⟨n, hn⟩
      have h := congrArg Complex.re hn
      simp at h
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith [hρ.2.1]
    · intro h1
      have h := hρ.2.2
      rw [h1] at h
      norm_num at h
  have h14' : ∀ ρ : ℂ, RvM.IsNontrivialZero ρ → 0 < ρ.im → 14 ≤ ρ.im := by
    intro ρ hρ hi
    by_contra hlt
    push Not at hlt
    rcases le_or_gt ρ.im 2 with h2 | h2
    · exact zeta_ne_zero_of_mem_strip_of_abs_im_le_two ρ hρ.2.1 hρ.2.2
        (by rw [abs_of_pos hi]; exact h2) hρ.1
    · exact TaoFivePrimes.zeta_ne_zero_strip_im_two_to_fourteen ρ hρ.2.1 hρ.2.2 h2.le hlt.le hρ.1
  have hlow' : ∀ t : ℝ, 14 ≤ t → t ≤ 2500 →
      (RvM.Ncount 4 t : ℝ) ≤ RvM.countingMain t + 5 / 2 := by
    intro t h1 h2
    rw [← RvM.Ncount_zero_eq_four]
    exact hlow t h1 h2
  exact SchoenfeldN.psi_large hRH' hlow' h14' x hx
