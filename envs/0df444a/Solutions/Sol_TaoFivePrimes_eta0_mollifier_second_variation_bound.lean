-- Prove2me | solution 1 for TaoFivePrimes.eta0_mollifier_second_variation_bound
-- status  : ACCEPTED   (prove)
-- author  : @radokirov
-- created : 2026-09-29T19:16:42.597385+00:00
-- url     : https://prove2.me/submissions/4c0e7def-a2fd-4214-9a5a-757b9a3a26e2

import Mathlib
import Definitions.Def_TaoFivePrimes_RepresentationCount
import Theorems.Thm_TaoFivePrimes_eta0_mollifier_second_derivative_identity

open MeasureTheory
open scoped Convolution

/-- The absolutely continuous part of `|η₀''|`: the kernel `4/t²` on `(1/4, 1]`. -/
private noncomputable def kAC : ℝ → ℝ :=
  Set.indicator (Set.Ioc (1 / 4 : ℝ) 1) (fun t => 4 / t ^ 2)

private lemma kAC_integrable : Integrable kAC := by
  unfold kAC
  rw [integrable_indicator_iff measurableSet_Ioc]
  have hc : ContinuousOn (fun t : ℝ => 4 / t ^ 2) (Set.Icc (1 / 4 : ℝ) 1) := by
    apply ContinuousOn.div continuousOn_const (continuousOn_id.pow 2)
    intro t ht
    have : (0 : ℝ) < t := lt_of_lt_of_le (by norm_num) ht.1
    exact pow_ne_zero 2 this.ne'
  exact (hc.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self

private lemma kAC_integral : (∫ t, kAC t) = 12 := by
  unfold kAC
  rw [integral_indicator measurableSet_Ioc, ← intervalIntegral.integral_of_le (by norm_num)]
  have hderiv : ∀ t ∈ Set.uIcc (1 / 4 : ℝ) 1,
      HasDerivAt (fun t : ℝ => -4 * t⁻¹) (4 / t ^ 2) t := by
    intro t ht
    rw [Set.uIcc_of_le (by norm_num)] at ht
    have htne : t ≠ 0 := by
      have : (0 : ℝ) < t := lt_of_lt_of_le (by norm_num) ht.1
      exact this.ne'
    exact ((hasDerivAt_inv htne).const_mul (-4)).congr_deriv (by ring)
  have hint : IntervalIntegrable (fun t : ℝ => 4 / t ^ 2) volume (1 / 4) 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num)]
    apply ContinuousOn.div continuousOn_const (continuousOn_id.pow 2)
    intro t ht
    have : (0 : ℝ) < t := lt_of_lt_of_le (by norm_num) ht.1
    exact pow_ne_zero 2 this.ne'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  norm_num

theorem solution (φ : ℝ → ℝ)
    (hc : HasCompactSupport φ) (hs : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hp : ∀ x, 0 ≤ φ x) (hm : (∫ x, φ x) = 1) :
    (∫ x, |deriv (deriv (TaoFivePrimes.eta0 ⋆ φ)) x|) ≤ 48 := by
  have hcont : Continuous φ := hs.continuous
  have hφi : Integrable φ := hcont.integrable_of_hasCompactSupport hc
  -- the continuous integrand on the fixed interval
  have hII : ∀ x (a b : ℝ), 1 / 4 ≤ a → a ≤ b →
      IntervalIntegrable (fun t : ℝ => 4 / t ^ 2 * φ (x - t)) volume a b := by
    intro x a b ha hab
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    apply ContinuousOn.mul
    · apply ContinuousOn.div continuousOn_const (continuousOn_id.pow 2)
      intro t ht
      have : (0 : ℝ) < t := lt_of_lt_of_le (by norm_num) (ha.trans ht.1)
      exact pow_ne_zero 2 this.ne'
    · exact (hcont.comp (continuous_const.sub continuous_id)).continuousOn
  -- the convolution with the kernel is the interval integral over `(1/4, 1]`
  have hconv : ∀ x, (kAC ⋆ φ) x = ∫ t in (1 / 4 : ℝ)..1, 4 / t ^ 2 * φ (x - t) := by
    intro x
    rw [convolution_def, intervalIntegral.integral_of_le (by norm_num),
      ← integral_indicator measurableSet_Ioc]
    congr 1
    ext t
    unfold kAC
    simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
    by_cases ht : t ∈ Set.Ioc (1 / 4 : ℝ) 1
    · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht]
    · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht, zero_mul]
  -- pointwise domination
  set g : ℝ → ℝ := fun x =>
    16 * φ (x - 1 / 4) + 16 * φ (x - 1 / 2) + 4 * φ (x - 1) + (kAC ⋆ φ) x with hg
  have hpt : ∀ x, |deriv (deriv (TaoFivePrimes.eta0 ⋆ φ)) x| ≤ g x := by
    intro x
    rw [TaoFivePrimes.eta0_mollifier_second_derivative_identity φ hc hs x, hg]
    simp only
    rw [hconv x]
    set A := ∫ t in (1 / 2 : ℝ)..1, 4 / t ^ 2 * φ (x - t)
    set B := ∫ t in (1 / 4 : ℝ)..(1 / 2), 4 / t ^ 2 * φ (x - t)
    have hsplit : (∫ t in (1 / 4 : ℝ)..1, 4 / t ^ 2 * φ (x - t)) = B + A :=
      (intervalIntegral.integral_add_adjacent_intervals
        (hII x _ _ le_rfl (by norm_num)) (hII x _ _ (by norm_num) (by norm_num))).symm
    have hA : 0 ≤ A := intervalIntegral.integral_nonneg (by norm_num)
      (fun t _ => mul_nonneg (by positivity) (hp _))
    have hB : 0 ≤ B := intervalIntegral.integral_nonneg (by norm_num)
      (fun t _ => mul_nonneg (by positivity) (hp _))
    rw [hsplit]
    have h1 := hp (x - 1 / 4)
    have h2 := hp (x - 1 / 2)
    have h3 := hp (x - 1)
    rw [abs_le]
    constructor <;> linarith
  -- integrability of the dominating function
  have hkφ : Integrable (kAC ⋆ φ) := kAC_integrable.integrable_convolution _ hφi
  have ht : ∀ a : ℝ, Integrable (fun x => φ (x - a)) := fun a => hφi.comp_sub_right a
  have h1 : Integrable (fun x => 16 * φ (x - 1 / 4)) := (ht _).const_mul 16
  have h2 : Integrable (fun x => 16 * φ (x - 1 / 2)) := (ht _).const_mul 16
  have h3 : Integrable (fun x => 4 * φ (x - 1)) := (ht _).const_mul 4
  have h12 : Integrable (fun x => 16 * φ (x - 1 / 4) + 16 * φ (x - 1 / 2)) := h1.add h2
  have h123 : Integrable
      (fun x => 16 * φ (x - 1 / 4) + 16 * φ (x - 1 / 2) + 4 * φ (x - 1)) := h12.add h3
  have hgi : Integrable g := h123.add hkφ
  have hgint : (∫ x, g x) = 48 := by
    rw [hg]
    simp only
    rw [integral_add h123 hkφ, integral_add h12 h3, integral_add h1 h2,
      integral_const_mul, integral_const_mul, integral_const_mul,
      integral_sub_right_eq_self, integral_sub_right_eq_self, integral_sub_right_eq_self,
      integral_convolution (L := ContinuousLinearMap.lsmul ℝ ℝ) (μ := volume) (ν := volume) kAC_integrable hφi, kAC_integral, hm]
    simp
    norm_num
  calc (∫ x, |deriv (deriv (TaoFivePrimes.eta0 ⋆ φ)) x|)
      ≤ ∫ x, g x :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => abs_nonneg _) hgi
          (Filter.Eventually.of_forall hpt)
    _ = 48 := hgint
