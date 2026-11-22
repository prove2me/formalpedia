-- Prove2me | solution 1 for SchauderBasis.tendstoUniformly_iteratedDeriv_fourier_partialSum
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T18:21:04.258182+00:00
-- url     : https://prove2.me/submissions/fde91542-abac-4f35-bafe-26c1e5755bdb

import Mathlib

open Filter Topology
open scoped ContDiff

set_option autoImplicit false

namespace Sol_SchauderBasis_tendstoUniformly_iteratedDeriv_fourier_partialSum

open Function Set
open scoped Interval

/-- Differentiation of a smooth `T`-periodic function multiplies its `m`-th Fourier coefficient
by `2πim/T`. -/
theorem fourierCoeffOn_deriv {T : ℝ} (hT : 0 < T) {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hper : Periodic f T) (m : ℤ) :
    fourierCoeffOn hT (deriv f) m =
      (2 * Real.pi * Complex.I * m / T) * fourierCoeffOn hT f m := by
  have : Fact (0 < T) := ⟨hT⟩
  obtain ⟨hd, hd'⟩ := contDiff_infty_iff_deriv.mp hf
  have hcont := hd'.continuous
  have hend : f T = f 0 := by simpa using hper 0
  let e (x : ℝ) := fourier (-m) (x : AddCircle T)
  let a : ℂ := 2 * Real.pi * Complex.I * m / T
  have he (x : ℝ) : HasDerivAt e (-a * e x) x := by
    have := hasDerivAt_fourier_neg T m x
    simp only [e, a]
    convert this using 1
    ring
  have hecont : Continuous e := (fourier (-m)).continuous.comp (AddCircle.continuous_mk' T)
  have heend : e T = e 0 := by simp only [e, AddCircle.coe_period, AddCircle.coe_zero]
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (a := 0) (b := T) hecont.continuousOn hf.continuous.continuousOn
    (fun x _ ↦ he x) (fun x _ ↦ (hd x).hasDerivAt)
    ((continuous_const.mul hecont).intervalIntegrable 0 T) (hcont.intervalIntegrable 0 T)
  rw [hend, heend, sub_self, zero_sub] at h
  simp_rw [mul_assoc, intervalIntegral.integral_const_mul, neg_mul, neg_neg] at h
  have hcoeff (g : ℝ → ℂ) :
      fourierCoeffOn hT g m = (1 / T) * ∫ x in (0:ℝ)..T, e x * g x := by
    rw [fourierCoeffOn_eq_integral, sub_zero]
    simp only [smul_eq_mul, e, Complex.real_smul, Complex.ofReal_div, Complex.ofReal_one]
  rw [hcoeff, hcoeff, h]
  ring

theorem deriv_periodic {T : ℝ} {f : ℝ → ℂ} (hf : Periodic f T) : Periodic (deriv f) T := by
  intro x
  rw [← deriv_comp_add_const, show (fun y ↦ f (y + T)) = f from funext hf]

theorem norm_fourierCoeffOn_le {T : ℝ} (hT : 0 < T) {g : ℝ → ℂ} {C : ℝ}
    (hC : ∀ x ∈ uIcc (0 : ℝ) T, ‖g x‖ ≤ C) (m : ℤ) :
    ‖fourierCoeffOn hT g m‖ ≤ C := by
  have : Fact (0 < T) := ⟨hT⟩
  rw [fourierCoeffOn_eq_integral, sub_zero]
  have hb : ∀ x ∈ uIoc (0 : ℝ) T,
      ‖fourier (-m) (x : AddCircle T) • g x‖ ≤ C := by
    intro x hx
    rw [norm_smul, fourier_apply, Circle.norm_coe, one_mul]
    exact hC x (uIoc_subset_uIcc hx)
  have := intervalIntegral.norm_integral_le_of_norm_le_const hb
  rw [norm_smul, sub_zero, abs_of_pos hT] at *
  rw [norm_div, norm_one, Real.norm_of_nonneg hT.le]
  calc 1 / T * ‖∫ x in (0:ℝ)..T, fourier (-m) (x : AddCircle T) • g x‖
      ≤ 1 / T * (C * T) := by gcongr
    _ = C := by field_simp

theorem summable_fourierCoeffOn {T : ℝ} (hT : 0 < T) {φ : ℝ → ℂ} (hφ : ContDiff ℝ ∞ φ)
    (hper : Periodic φ T) : Summable (fourierCoeffOn hT φ) := by
  have hd := (contDiff_infty_iff_deriv.mp hφ).2
  have hdd := (contDiff_infty_iff_deriv.mp hd).2
  obtain ⟨C, hC⟩ := isCompact_uIcc.exists_bound_of_continuousOn
    (s := uIcc (0 : ℝ) T) hdd.continuous.continuousOn
  have hbound (m : ℤ) : ‖fourierCoeffOn hT (deriv (deriv φ)) m‖ ≤ C :=
    norm_fourierCoeffOn_le hT hC m
  let a : ℂ := 2 * Real.pi * Complex.I / T
  have ha : 0 < ‖a‖ := norm_pos_iff.mpr (by simp [a, Real.pi_ne_zero, hT.ne'])
  have hp := Real.summable_one_div_int_pow.mpr (by decide : 1 < (2 : ℕ))
  refine (hp.mul_left (C / ‖a‖ ^ 2)).of_norm_bounded_eventually ?_
  filter_upwards [eventually_cofinite_ne (0 : ℤ)] with m hm
  specialize hbound m
  rw [fourierCoeffOn_deriv hT hd (deriv_periodic hper),
    fourierCoeffOn_deriv hT hφ hper] at hbound
  have hfac : (2 * Real.pi * Complex.I * m / T) = a * m := by
    simp only [a]; ring
  rw [hfac, ← mul_assoc, norm_mul, norm_mul, norm_mul, Complex.norm_intCast] at hbound
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  have hpos : 0 < ‖a‖ ^ 2 * (m : ℝ) ^ 2 := by positivity
  rw [mul_one_div, div_div, le_div_iff₀ hpos]
  have : ‖a‖ * |(m : ℝ)| * (‖a‖ * |(m : ℝ)|) = ‖a‖ ^ 2 * (m : ℝ) ^ 2 := by
    rw [← sq_abs (m : ℝ)]; ring
  nlinarith [hbound, this, norm_nonneg (fourierCoeffOn hT φ m)]

end Sol_SchauderBasis_tendstoUniformly_iteratedDeriv_fourier_partialSum

open Sol_SchauderBasis_tendstoUniformly_iteratedDeriv_fourier_partialSum in
theorem solution
    (T : ℝ) (hT : 0 < T) (φ : ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ) (hper : Function.Periodic φ T)
    (k : ℕ) :
    TendstoUniformly
      (fun s : Finset ℤ => iteratedDeriv k (fun t : ℝ =>
        ∑ m ∈ s, fourierCoeffOn hT φ m * fourier m (t : AddCircle T)))
      (iteratedDeriv k φ) atTop := by
  have : Fact (0 < T) := ⟨hT⟩
  induction k generalizing φ with
  | zero =>
      simp only [iteratedDeriv_zero]
      let F : C(AddCircle T, ℂ) := ⟨hper.lift, continuous_coinduced_dom.mpr hφ.continuous⟩
      have hcoeff (m : ℤ) : fourierCoeff F m = fourierCoeffOn hT φ m := by
        rw [fourierCoeff_eq_intervalIntegral _ _ 0, fourierCoeffOn_eq_integral, sub_zero]
        simp [F, Function.Periodic.lift_coe]
      have hs : Summable (fourierCoeff F) := by
        rw [show fourierCoeff F = fourierCoeffOn hT φ from funext hcoeff]
        exact summable_fourierCoeffOn hT hφ hper
      have hu := ContinuousMap.tendsto_iff_tendstoUniformly.mp
        (hasSum_fourier_series_of_summable hs)
      have hlift := hu.comp (fun t : ℝ ↦ (t : AddCircle T))
      simp only [Function.comp_def, ContinuousMap.sum_apply, ContinuousMap.smul_apply,
        smul_eq_mul, hcoeff] at hlift
      simpa only [F, ContinuousMap.coe_mk, Function.Periodic.lift_coe,
        SummationFilter.unconditional_filter] using hlift
  | succ k ih =>
      simp only [iteratedDeriv_succ']
      have hsum (s : Finset ℤ) :
          deriv (fun t : ℝ ↦ ∑ m ∈ s, fourierCoeffOn hT φ m *
            fourier m (t : AddCircle T)) =
          fun t : ℝ ↦ ∑ m ∈ s, fourierCoeffOn hT (deriv φ) m *
            fourier m (t : AddCircle T) := by
        funext t
        apply HasDerivAt.deriv
        apply HasDerivAt.fun_sum
        intro m _
        rw [fourierCoeffOn_deriv hT hφ hper]
        exact ((hasDerivAt_fourier T m t).const_mul (fourierCoeffOn hT φ m)).congr_deriv
          (by ring)
      simp only [hsum]
      exact ih _ (contDiff_infty_iff_deriv.mp hφ).2 (deriv_periodic hper)
