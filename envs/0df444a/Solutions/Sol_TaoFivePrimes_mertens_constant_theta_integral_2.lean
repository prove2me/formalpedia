-- Prove2me | solution 2 for TaoFivePrimes.mertens_constant_theta_integral
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-27T23:46:01.609864+00:00
-- url     : https://prove2.me/submissions/45a4e1d8-162c-44e5-b63d-6377e3f2a908
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_TaoFivePrimes_reciprocal_primes_theta_partial_summation
import Theorems.Thm_TaoFivePrimes_dusart_theta_error_log_four
import Theorems.Thm_TaoFivePrimes_reciprocal_prime_mertens_limit
import Mathlib
open MeasureTheory Set Filter
open scoped Topology

private theorem majorant_integrable (x : ℝ) (hx : 1 < x) :
    IntegrableOn (fun t : ℝ => 100 * (Real.log t + 1) / (t * (Real.log t) ^ 6)) (Ioi x) := by
  let g : ℝ → ℝ := fun t => -(25 / (Real.log t) ^ 4 + 20 / (Real.log t) ^ 5)
  let d : ℝ → ℝ := fun t => 100 * (Real.log t + 1) / (t * (Real.log t) ^ 6)
  have hd : ∀ t ∈ Ici x, HasDerivAt g (d t) t := by
    intro t ht
    have htpos : 0 < t := lt_trans zero_lt_one (lt_of_lt_of_le hx ht)
    have hl : Real.log t ≠ 0 := ne_of_gt (Real.log_pos (lt_of_lt_of_le hx ht))
    have h4 := (hasDerivAt_const t (25 : ℝ)).div
      ((Real.hasDerivAt_log htpos.ne').pow 4) (pow_ne_zero 4 hl)
    have h5 := (hasDerivAt_const t (20 : ℝ)).div
      ((Real.hasDerivAt_log htpos.ne').pow 5) (pow_ne_zero 5 hl)
    convert (h4.add h5).neg using 1 <;> (try rfl) <;> (try dsimp [g, d]) <;>
      field_simp [htpos.ne', hl] <;> ring
  have hdpos : ∀ t ∈ Ioi x, 0 ≤ d t := by
    intro t ht
    have htpos : 0 < t := lt_trans zero_lt_one (lt_trans hx ht)
    have hl : 0 < Real.log t := Real.log_pos (lt_trans hx ht)
    dsimp [d]
    positivity
  have hlim : Tendsto g atTop (𝓝 0) := by
    have hi : Tendsto (fun t : ℝ => (Real.log t)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
    have hh := ((hi.pow 4).const_mul 25 |>.add ((hi.pow 5).const_mul 20)).neg
    simpa [g, div_eq_mul_inv, inv_pow] using hh
  have hdi : IntegrableOn d (Ioi x) := integrableOn_Ioi_deriv_of_nonneg' hd hdpos hlim
  exact hdi

private theorem global_kernel_integrable
    (hθ : ∀ t : ℝ, 2 ≤ t →
      |(∑ p ∈ Nat.primesLE ⌊t⌋₊, Real.log (p : ℝ)) - t| ≤
        160 * t / (Real.log t) ^ 4) :
    IntegrableOn
      (fun t : ℝ => (((∑ p ∈ Nat.primesLE ⌊t⌋₊, Real.log (p : ℝ)) - t) *
        (Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2))) (Ioi (2 : ℝ)) := by
  let θ : ℝ → ℝ := fun t => ∑ p ∈ Nat.primesLE ⌊t⌋₊, Real.log (p : ℝ)
  let R : ℝ → ℝ := fun t => (θ t - t) * (Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2)
  have hθmeas : Measurable θ :=
    (measurable_of_countable (fun n : ℕ => ∑ p ∈ Nat.primesLE n, Real.log (p : ℝ))).comp Nat.measurable_floor
  have hRmeas : Measurable R := by dsimp [R]; fun_prop
  apply ((majorant_integrable 2 (by norm_num)).const_mul (8 / 5 : ℝ)).mono' hRmeas.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have htt : 2 < t := ht
  have htpos : 0 < t := by linarith
  have hl : 0 < Real.log t := Real.log_pos (by linarith)
  have hbound := hθ t ht.le
  dsimp [R]
  rw [abs_div, abs_mul, abs_of_pos (by positivity : 0 < Real.log t + 1),
    abs_of_pos (by positivity : 0 < t ^ 2 * Real.log t ^ 2)]
  calc
    |θ t - t| * (Real.log t + 1) / (t ^ 2 * Real.log t ^ 2) ≤
        (160 * t / Real.log t ^ 4) * (Real.log t + 1) / (t ^ 2 * Real.log t ^ 2) := by
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hbound (by positivity)) (by positivity)
    _ = (8 / 5 : ℝ) * (100 * (Real.log t + 1) / (t * Real.log t ^ 6)) := by
      field_simp [htpos.ne', hl.ne'] <;> ring

private theorem identity_with_constant (B : ℝ)
    (hconst : IntegrableOn
      (fun t : ℝ => (((∑ p ∈ Nat.primesLE ⌊t⌋₊, Real.log (p : ℝ)) - t) *
        (Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2))) (Set.Ioi (2 : ℝ)) ∧
      B = 1 / Real.log 2 - Real.log (Real.log 2) +
      ∫ t in Set.Ioi (2 : ℝ),
        (((∑ p ∈ Nat.primesLE ⌊t⌋₊, Real.log (p : ℝ)) - t) *
          (Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2)))
    (x : ℝ) (hx : 2 ≤ x) :
    (∑ p ∈ Nat.primesLE ⌊x⌋₊, 1 / (p : ℝ)) =
      Real.log (Real.log x) +
        B +
      ((∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log (p : ℝ)) - x) / (x * Real.log x) -
      ∫ t in Set.Ioi x,
        (((∑ p ∈ Nat.primesLE ⌊t⌋₊, Real.log (p : ℝ)) - t) *
          (Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2)) := by
  let θ : ℝ → ℝ := fun t => ∑ p ∈ Nat.primesLE ⌊t⌋₊, Real.log (p : ℝ)
  let R : ℝ → ℝ := fun t => (θ t - t) * (Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2)
  let K : ℝ → ℝ := fun t => t * (Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2)
  let F : ℝ → ℝ := fun t => Real.log (Real.log t) - 1 / Real.log t
  have hc := hconst
  change IntegrableOn R (Ioi 2) ∧ _ = _ + ∫ t in Ioi 2, R t at hc
  have hkcont : ContinuousOn K (Icc 2 x) := by
    intro t ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hl0 : Real.log t ≠ 0 := ne_of_gt (Real.log_pos (by linarith [ht.1]))
    exact ((continuousAt_id.mul ((Real.continuousAt_log ht0).add continuousAt_const)).div
      ((continuousAt_id.pow 2).mul ((Real.continuousAt_log ht0).pow 2))
      (mul_ne_zero (pow_ne_zero 2 ht0) (pow_ne_zero 2 hl0))).continuousWithinAt
  have hkinterval : IntervalIntegrable K volume 2 x := hkcont.intervalIntegrable_of_Icc hx
  have hkint : IntegrableOn K (Ioc 2 x) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hx).mp hkinterval
  have hderiv : ∀ t ∈ uIcc (2 : ℝ) x, HasDerivAt F (K t) t := by
    intro t ht
    rw [uIcc_of_le hx] at ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hl0 : Real.log t ≠ 0 := ne_of_gt (Real.log_pos (by linarith [ht.1]))
    have hloglog := (Real.hasDerivAt_log hl0).comp t (Real.hasDerivAt_log ht0)
    have hinv := (hasDerivAt_const t (1 : ℝ)).div (Real.hasDerivAt_log ht0) hl0
    convert hloglog.sub hinv using 1 <;> (try rfl) <;> (try dsimp [F, K]) <;> field_simp [ht0, hl0] <;> ring
  have hmain := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hkinterval
  rw [intervalIntegral.integral_of_le hx] at hmain
  have hRint : IntegrableOn R (Ioc 2 x) := hc.1.mono_set (by
    intro t ht; exact ht.1)
  have hRx : IntegrableOn R (Ioi x) := hc.1.mono_set (by
    intro t ht; exact lt_of_le_of_lt hx ht)
  have hdisj : Disjoint (Ioc (2 : ℝ) x) (Ioi x) := by
    apply disjoint_left.mpr
    intro t ht hu
    exact (not_lt_of_ge ht.2) hu
  have hsets : Ioc (2 : ℝ) x ∪ Ioi x = Ioi 2 := by
    ext t
    constructor
    · intro ht
      rcases ht with ht | ht
      · exact ht.1
      · exact lt_of_le_of_lt hx ht
    · intro ht
      by_cases htx : t ≤ x
      · exact Or.inl ⟨ht, htx⟩
      · exact Or.inr (lt_of_not_ge htx)
  have hsplit := setIntegral_union hdisj measurableSet_Ioi hRint hRx
  rw [hsets] at hsplit
  have hsumint : (∫ t in Ioc (2 : ℝ) x, θ t * (Real.log t + 1) /
      (t ^ 2 * (Real.log t) ^ 2)) = (∫ t in Ioc (2 : ℝ) x, R t) +
      ∫ t in Ioc (2 : ℝ) x, K t := by
    rw [← integral_add hRint hkint]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    dsimp [R, K]
    ring
  have hpartial := TaoFivePrimes.reciprocal_primes_theta_partial_summation x hx
  change (∑ p ∈ Nat.primesLE ⌊x⌋₊, 1 / (p : ℝ)) = θ x / (x * Real.log x) +
    ∫ t in Ioc (2 : ℝ) x, θ t * (Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2) at hpartial
  rw [hsumint] at hpartial
  have hx0 : x ≠ 0 := by linarith
  have hl0 : Real.log x ≠ 0 := ne_of_gt (Real.log_pos (by linarith))
  have hend : θ x / (x * Real.log x) = (θ x - x) / (x * Real.log x) + 1 / Real.log x := by
    field_simp [hx0, hl0]
    <;> ring
  rw [hend] at hpartial
  dsimp [F] at hmain
  change (∑ p ∈ Nat.primesLE ⌊x⌋₊, 1 / (p : ℝ)) = _ + (θ x - x) / (x * Real.log x) - ∫ t in Ioi x, R t
  linarith [hc.2]


theorem solution :
    MeasureTheory.IntegrableOn
      (fun t : ℝ => (((∑ p ∈ Nat.primesLE ⌊t⌋₊, Real.log (p : ℝ)) - t) *
        (Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2))) (Set.Ioi (2 : ℝ)) ∧
    (Real.eulerMascheroniConstant +
      ∑' p : Nat.Primes, (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ))) =
      1 / Real.log 2 - Real.log (Real.log 2) +
      ∫ t in Set.Ioi (2 : ℝ),
        (((∑ p ∈ Nat.primesLE ⌊t⌋₊, Real.log (p : ℝ)) - t) *
          (Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2)) := by
  let θ : ℝ → ℝ := fun t => ∑ p ∈ Nat.primesLE ⌊t⌋₊, Real.log (p : ℝ)
  let R : ℝ → ℝ := fun t => (θ t - t) * (Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2)
  let C : ℝ := 1 / Real.log 2 - Real.log (Real.log 2) + ∫ t in Ioi 2, R t
  have hθ : ∀ t : ℝ, 2 ≤ t → |θ t - t| ≤ 160 * t / (Real.log t)^4 := by
    intro t ht
    have hs := TaoFivePrimes.dusart_theta_error_log_four t ht
    have htpos : 0 < t := by linarith
    have hp : 0 ≤ t / (Real.log t)^4 := by positivity
    have hb : (1513 / 10 : ℝ) * t / (Real.log t)^4 ≤ 160 * t / (Real.log t)^4 :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by norm_num : (1513 / 10 : ℝ) ≤ 160) htpos.le)
        (by positivity)
    exact hs.trans hb
  have hint := global_kernel_integrable hθ
  refine ⟨hint, ?_⟩
  have hsmall : Tendsto (fun t : ℝ => 160 / (Real.log t)^5) atTop (𝓝 0) := by
    have hi : Tendsto (fun t : ℝ => (Real.log t)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
    simpa [div_eq_mul_inv, inv_pow] using (hi.pow 5).const_mul 160
  have hend : Tendsto (fun t : ℝ => (θ t - t) / (t * Real.log t)) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ hsmall
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with t ht
    have htpos : 0 < t := by linarith
    have hl : 0 < Real.log t := Real.log_pos (by linarith)
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (mul_pos htpos hl)]
    calc
      |θ t - t| / (t * Real.log t) ≤ (160 * t / (Real.log t)^4) / (t * Real.log t) :=
        div_le_div_of_nonneg_right (hθ t ht) (le_of_lt (mul_pos htpos hl))
      _ = 160 / (Real.log t)^5 := by field_simp [htpos.ne', hl.ne'] <;> ring
  have htail : Tendsto (fun t : ℝ => ∫ u in Ioi t, R u) atTop (𝓝 0) :=
    tendsto_integral_Ioi_zero tendsto_id
  have hlim : Tendsto (fun t : ℝ =>
      (∑ p ∈ Nat.primesLE ⌊t⌋₊, 1 / (p : ℝ)) - Real.log (Real.log t)) atTop (𝓝 C) := by
    have haux := (hend.const_add C).sub htail
    have haux' : Tendsto (fun t : ℝ => C + (θ t - t) / (t * Real.log t) - ∫ u in Ioi t, R u)
        atTop (𝓝 C) := by simpa using haux
    apply haux'.congr'
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with t ht
    have hid := identity_with_constant C ⟨hint, rfl⟩ t ht
    change (∑ p ∈ Nat.primesLE ⌊t⌋₊, 1 / (p : ℝ)) =
      Real.log (Real.log t) + C + (θ t - t) / (t * Real.log t) - ∫ u in Ioi t, R u at hid
    linarith
  exact tendsto_nhds_unique TaoFivePrimes.reciprocal_prime_mertens_limit hlim
