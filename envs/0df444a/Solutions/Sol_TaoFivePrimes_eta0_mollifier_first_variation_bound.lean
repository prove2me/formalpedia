-- Prove2me | solution 1 for TaoFivePrimes.eta0_mollifier_first_variation_bound
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-27T23:59:06.841788+00:00
-- url     : https://prove2.me/submissions/a362ca5c-333a-4507-8689-46833e695649

import Mathlib
import Theorems.Thm_TaoFivePrimes_eta0_lipschitz_sixteen
import Definitions.Def_TaoFivePrimes_RepresentationCount

open MeasureTheory
open scoped Convolution
open TaoFivePrimes

namespace Eta0MollifierFirst

theorem eta0_eq_zero_of_le {t : ℝ} (h : t ≤ 1/4) : eta0 t = 0 := by
  unfold eta0
  by_cases ht : 0 < t
  · rw [if_pos ht, max_eq_left, mul_zero]
    have h2 : Real.log (2*t) ≤ Real.log (1/2) := Real.log_le_log (by linarith) (by linarith)
    have h3 : Real.log (1/2 : ℝ) = -Real.log 2 := by
      rw [show (1/2 : ℝ) = (2:ℝ)⁻¹ by norm_num, Real.log_inv]
    rw [h3] at h2
    linarith [neg_le_abs (Real.log (2*t))]
  · rw [if_neg ht]

theorem eta0_eq_zero_of_ge {t : ℝ} (h : 1 ≤ t) : eta0 t = 0 := by
  unfold eta0
  have ht : 0 < t := by linarith
  rw [if_pos ht, max_eq_left, mul_zero]
  have h2 : Real.log 2 ≤ Real.log (2*t) := Real.log_le_log (by norm_num) (by linarith)
  linarith [le_abs_self (Real.log (2*t))]

theorem eta0_on_left {t : ℝ} (h1 : 1/4 ≤ t) (h2 : t ≤ 1/2) :
    eta0 t = 4 * (2 * Real.log 2 + Real.log t) := by
  have ht : 0 < t := by linarith
  have hlog : Real.log (2*t) = Real.log 2 + Real.log t :=
    Real.log_mul (by norm_num) (ne_of_gt ht)
  have hle : Real.log (2*t) ≤ 0 := by
    rw [show (0:ℝ) = Real.log 1 by simp]
    exact Real.log_le_log (by linarith) (by linarith)
  have hge : (0:ℝ) ≤ 2 * Real.log 2 + Real.log t := by
    have h : Real.log (1/4 : ℝ) ≤ Real.log t := Real.log_le_log (by norm_num) h1
    have h4 : Real.log (1/4 : ℝ) = -(2 * Real.log 2) := by
      rw [show (1/4 : ℝ) = (2:ℝ)⁻¹ ^ 2 by norm_num, Real.log_pow, Real.log_inv]
      push_cast; ring
    linarith [h4 ▸ h]
  unfold eta0
  rw [if_pos ht, abs_of_nonpos hle, hlog, max_eq_right (by linarith)]
  ring

theorem eta0_on_right {t : ℝ} (h1 : 1/2 ≤ t) (h2 : t ≤ 1) :
    eta0 t = -4 * Real.log t := by
  have ht : 0 < t := by linarith
  have hlog : Real.log (2*t) = Real.log 2 + Real.log t :=
    Real.log_mul (by norm_num) (ne_of_gt ht)
  have hge : (0:ℝ) ≤ Real.log (2*t) := by
    rw [show (0:ℝ) = Real.log 1 by simp]
    exact Real.log_le_log (by norm_num) (by linarith)
  have hlt : Real.log t ≤ 0 := by
    rw [show (0:ℝ) = Real.log 1 by simp]
    exact Real.log_le_log ht h2
  unfold eta0
  rw [if_pos ht, abs_of_nonneg hge, hlog, max_eq_right (by linarith)]
  ring

private lemma branch_parts (a b C D : ℝ) (ha : 0 < a) (hb : 0 < b)
    (f f' : ℝ → ℝ) (hf : ∀ t, HasDerivAt f (f' t) t) (hc : Continuous f') :
    (∫ t in a..b, (C + D * Real.log t) * f' t) =
      (C + D * Real.log b) * f b - (C + D * Real.log a) * f a -
        ∫ t in a..b, (D / t) * f t := by
  have hn : ∀ t ∈ Set.uIcc a b, t ≠ 0 := by
    intro t ht
    have hp : 0 < min a b := lt_min ha hb
    exact ne_of_gt (lt_of_lt_of_le hp ht.1)
  apply intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u' := fun t => D / t)
  · intro t ht
    simpa only [div_eq_mul_inv] using
      ((Real.hasDerivAt_log (hn t ht)).const_mul D).const_add C
  · intro t ht; exact hf t
  · exact (continuousOn_const.div continuousOn_id hn).intervalIntegrable
  · exact hc.intervalIntegrable a b

private lemma weak_first (f f' : ℝ → ℝ)
    (hf : ∀ t, HasDerivAt f (f' t) t) (hc : Continuous f') :
    (∫ t in (1 / 4 : ℝ)..1, eta0 t * f' t) =
        (∫ t in (1 / 2 : ℝ)..1, (4 / t) * f t) -
        (∫ t in (1 / 4 : ℝ)..(1 / 2), (4 / t) * f t) := by
  have hleft := branch_parts (1/4) (1/2) (8 * Real.log 2) 4 (by norm_num)
    (by norm_num) f f' hf hc
  have hright := branch_parts (1/2) 1 0 (-4) (by norm_num)
    (by norm_num) f f' hf hc
  have loghalf : Real.log (1/2 : ℝ) = -Real.log 2 := by
    rw [show (1/2 : ℝ) = (2:ℝ)⁻¹ by norm_num, Real.log_inv]
  have logquarter : Real.log (1/4 : ℝ) = -(2 * Real.log 2) := by
    rw [show (1/4 : ℝ) = ((2:ℝ)⁻¹)^2 by norm_num, Real.log_pow, Real.log_inv]
    ring
  have hi : Continuous (fun t => eta0 t * f' t) := eta0_lipschitz_sixteen.continuous.mul hc
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hi.intervalIntegrable (1/4) (1/2)) (hi.intervalIntegrable (1/2) 1)]
  have heqleft : (∫ t in (1/4 : ℝ)..(1/2), eta0 t * f' t) =
      ∫ t in (1/4 : ℝ)..(1/2), (8 * Real.log 2 + 4 * Real.log t) * f' t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (1/4:ℝ) ≤ 1/2)] at ht
    change eta0 t * f' t = _
    rw [eta0_on_left ht.1 ht.2]
    ring
  have heqright : (∫ t in (1/2 : ℝ)..1, eta0 t * f' t) =
      ∫ t in (1/2 : ℝ)..1, (0 + -4 * Real.log t) * f' t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (1/2:ℝ) ≤ 1)] at ht
    change eta0 t * f' t = _
    rw [eta0_on_right ht.1 ht.2]
    ring
  rw [heqleft, heqright, hleft, hright, loghalf, logquarter]
  simp only [Real.log_one, mul_zero, add_zero, neg_div, neg_mul,
    intervalIntegral.integral_neg]
  ring

private lemma eta_support : Function.support eta0 ⊆ Set.Icc (1/4:ℝ) 1 := by
  intro t ht
  constructor
  · by_contra h
    exact ht (eta0_eq_zero_of_le (le_of_not_ge h))
  · by_contra h
    exact ht (eta0_eq_zero_of_ge (le_of_not_ge h))

private lemma eta_compact : HasCompactSupport eta0 := by
  apply HasCompactSupport.intro isCompact_Icc
  intro t ht
  by_contra hn
  exact ht (eta_support hn)

private lemma eta_integrable : Integrable eta0 :=
  eta0_lipschitz_sixteen.continuous.integrable_of_hasCompactSupport eta_compact

/-- Integration by parts transfers the mollifier derivative to the two branches
of the continuous logarithmic cutoff; the middle boundary terms cancel. -/
theorem kernel_first (φ : ℝ → ℝ)
    (hc : HasCompactSupport φ) (hs : ContDiff ℝ (⊤ : ℕ∞) φ) (x : ℝ) :
    deriv (eta0 ⋆ φ) x =
      (∫ t in (1/4:ℝ)..(1/2), (4/t) * φ (x-t)) -
      (∫ t in (1/2:ℝ)..1, (4/t) * φ (x-t)) := by
  have he : deriv (eta0 ⋆ φ) x = (eta0 ⋆ deriv φ) x :=
    (hc.hasDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ)
      eta_integrable.locallyIntegrable (hs.of_le (by simp)) x).deriv
  rw [he]
  change (∫ t, eta0 t * deriv φ (x-t)) = _
  have hz : ∀ t ∈ (Set.Icc (1/4:ℝ) 1)ᶜ,
      eta0 t * deriv φ (x-t) = 0 := by
    intro t ht
    have h : eta0 t = 0 := by
      by_contra h
      exact ht (eta_support h)
    rw [h, zero_mul]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz,
    integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (1/4:ℝ) ≤ 1)]
  have hφ : Differentiable ℝ φ := hs.differentiable (by simp)
  have h := weak_first (fun t => φ (x-t)) (fun t => -deriv φ (x-t))
    (fun t => by
      simpa [Function.comp_def] using (hφ (x-t)).hasDerivAt.comp t ((hasDerivAt_id t).const_sub x))
    (((contDiff_infty_iff_deriv.mp hs).2.continuous.comp (continuous_const.sub continuous_id)).neg)
  simp only [mul_neg, intervalIntegral.integral_neg] at h
  linarith only [h]

end Eta0MollifierFirst

namespace Eta0MollifierFirstVariation

private lemma interval_convolution_eq (a b : ℝ) (hab : a ≤ b)
    (k φ : ℝ → ℝ) (x : ℝ) :
    (∫ t in a..b, k t * φ (x-t)) =
      ((Set.Ioc a b).indicator k ⋆ φ) x := by
  rw [intervalIntegral.integral_of_le hab]
  change (∫ t in Set.Ioc a b, k t * φ (x-t)) =
    ∫ t, (Set.Ioc a b).indicator k t * φ (x-t)
  rw [← integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  filter_upwards with t
  by_cases ht : t ∈ Set.Ioc a b
  · simp only [Set.indicator_of_mem ht]
  · simp only [Set.indicator_of_notMem ht, zero_mul]

private lemma interval_convolution_integrable (a b : ℝ) (hab : a ≤ b)
    (k φ : ℝ → ℝ) (hk : IntervalIntegrable k volume a b) (hφ : Integrable φ) :
    Integrable (fun x => ∫ t in a..b, k t * φ (x-t)) := by
  have hi : Integrable ((Set.Ioc a b).indicator k) :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hk).integrable_indicator
      measurableSet_Ioc
  simpa only [interval_convolution_eq a b hab] using
    hi.integrable_convolution (ContinuousLinearMap.lsmul ℝ ℝ) hφ

private lemma interval_convolution_mass (a b : ℝ) (hab : a ≤ b)
    (k φ : ℝ → ℝ) (hk : IntervalIntegrable k volume a b) (hφ : Integrable φ)
    (hφ1 : (∫ t, φ t) = 1) :
    (∫ x, ∫ t in a..b, k t * φ (x-t)) = ∫ t in a..b, k t := by
  have hi : Integrable ((Set.Ioc a b).indicator k) :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hk).integrable_indicator
      measurableSet_Ioc
  simp only [interval_convolution_eq a b hab]
  rw [integral_convolution (ContinuousLinearMap.lsmul ℝ ℝ) hi hφ]
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul, hφ1, mul_one]
  rw [integral_indicator measurableSet_Ioc, intervalIntegral.integral_of_le hab]

private lemma weight_integrable (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ => 4 / t) volume a b := by
  apply ContinuousOn.intervalIntegrable
  apply continuousOn_const.div continuousOn_id
  intro t ht
  rw [Set.uIcc_of_le hab] at ht
  exact ne_of_gt (lt_of_lt_of_le ha ht.1)

private lemma weight_integral (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in a..b, (4:ℝ)/t) = 4 * Real.log b - 4 * Real.log a := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t : ℝ => 4 * Real.log t)
  · intro t ht
    have hn : t ≠ 0 := by
      rw [Set.uIcc_of_le hab] at ht
      exact ne_of_gt (lt_of_lt_of_le ha ht.1)
    simpa only [div_eq_mul_inv] using (Real.hasDerivAt_log hn).const_mul 4
  · exact weight_integrable a b ha hab

end Eta0MollifierFirstVariation

open Eta0MollifierFirstVariation

theorem solution (φ : ℝ → ℝ) (hc : HasCompactSupport φ)
    (hs : ContDiff ℝ (⊤ : ℕ∞) φ) (hp : ∀ x, 0 ≤ φ x)
    (hm : (∫ x, φ x) = 1) :
    (∫ x, |deriv (eta0 ⋆ φ) x|) ≤ 8 * Real.log 2 := by
  have hi : Integrable φ := hs.continuous.integrable_of_hasCompactSupport hc
  let A : ℝ → ℝ := fun x => ∫ t in (1/4:ℝ)..(1/2), 4/t * φ (x-t)
  let B : ℝ → ℝ := fun x => ∫ t in (1/2:ℝ)..1, 4/t * φ (x-t)
  have hAi : Integrable A := interval_convolution_integrable _ _ (by norm_num) _ _
    (weight_integrable _ _ (by norm_num) (by norm_num)) hi
  have hBi : Integrable B := interval_convolution_integrable _ _ (by norm_num) _ _
    (weight_integrable _ _ (by norm_num) (by norm_num)) hi
  have loghalf : Real.log (1/2 : ℝ) = -Real.log 2 := by
    rw [show (1/2 : ℝ) = (2:ℝ)⁻¹ by norm_num, Real.log_inv]
  have logquarter : Real.log (1/4 : ℝ) = -(2 * Real.log 2) := by
    rw [show (1/4 : ℝ) = ((2:ℝ)⁻¹)^2 by norm_num, Real.log_pow, Real.log_inv]
    ring
  have hAm : (∫ x, A x) = 4 * Real.log 2 := by
    rw [interval_convolution_mass _ _ (by norm_num) _ _
      (weight_integrable _ _ (by norm_num) (by norm_num)) hi hm,
      weight_integral _ _ (by norm_num) (by norm_num), loghalf, logquarter]
    ring
  have hBm : (∫ x, B x) = 4 * Real.log 2 := by
    rw [interval_convolution_mass _ _ (by norm_num) _ _
      (weight_integrable _ _ (by norm_num) (by norm_num)) hi hm,
      weight_integral _ _ (by norm_num) (by norm_num), loghalf, Real.log_one]
    ring
  have hAp : ∀ x, 0 ≤ A x := by
    intro x
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro t ht
    have ht0 : 0 ≤ t := by linarith [ht.1]
    exact mul_nonneg (div_nonneg (by norm_num) ht0) (hp _)
  have hBp : ∀ x, 0 ≤ B x := by
    intro x
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro t ht
    have ht0 : 0 ≤ t := by linarith [ht.1]
    exact mul_nonneg (div_nonneg (by norm_num) ht0) (hp _)
  have hpoint : ∀ x, |deriv (eta0 ⋆ φ) x| ≤ A x + B x := by
    intro x
    rw [Eta0MollifierFirst.kernel_first φ hc hs x]
    change |A x - B x| ≤ A x + B x
    rw [abs_le]
    constructor <;> linarith [hAp x, hBp x]
  have hmeas : AEStronglyMeasurable (fun x => |deriv (eta0 ⋆ φ) x|) volume :=
    by simpa only [Real.norm_eq_abs] using (aestronglyMeasurable_deriv (eta0 ⋆ φ) volume).norm
  have hdi : Integrable (fun x => |deriv (eta0 ⋆ φ) x|) :=
    (hAi.add hBi).mono' hmeas (Filter.Eventually.of_forall (fun x => by
      simpa only [Real.norm_eq_abs, abs_abs, Pi.add_apply] using hpoint x))
  calc
    (∫ x, |deriv (eta0 ⋆ φ) x|) ≤ ∫ x, A x + B x :=
      integral_mono hdi (hAi.add hBi) hpoint
    _ = 8 * Real.log 2 := by rw [integral_add hAi hBi, hAm, hBm]; ring
