-- Prove2me | solution 1 for RSInt.differentiable_integral_cpow
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T05:54:51.677199+00:00
-- url     : https://prove2.me/submissions/b820d65f-35a4-44ec-80b2-c85ee54fa9ad

import Definitions.Def_ArdaRH65K_RS_Entire
import Definitions.Def_ArdaRH65K_RS_Fold
import Definitions.Def_ArdaRH65K_RS_Kernel
import Definitions.Def_ArdaRH65K_RS_Mellin
import Definitions.Def_ArdaRH65K_RS_Strip
import Mathlib
import Theorems.Thm_RSInt_integrable_of_continuous_of_tail
/-  RS_Entire.lean -- lane RS, ANDURIL brick B2 (the Riemann-Siegel integral), part 5:
    holomorphy in `s` of the two Riemann-Siegel line integrals, and the chi factor.
    Mathlib-only (imports `RS_Fold`).

    ## Contents (no `sorry`, no `native_decide`, no new axioms)

      * `differentiable_integral_cpow` : a generic parametric-holomorphy lemma:
            s |-> int W(v) X(v)^s dv   is entire
        for continuous W with a Gaussian tail and a continuous line X in the slit plane with
        m <= |X v| <= alpha + beta |v|.
      * `differentiable_rsA`, `differentiable_rsB` : s |-> lineUp c (rsG x^(-s)) and
        s |-> lineDn c (rsH x^(s-1)) are entire for every c > 0 that is not an integer.
      * `rsChi s = pi^(s - 1/2) Gamma((1-s)/2) / Gamma(s/2)`, holomorphic off {1, 3, 5, ...}
        (`differentiableAt_rsChi`), with the Gamma-function identity
            rsChi s * Gamma s * (2 cos(pi s / 2)) = (2 pi)^s     (Re s > 0)
        (`rsChi_mul_Gamma_cos`, reflection + duplication).

    conjecture1_proved = False.
-/


open Complex MeasureTheory Filter Topology Set
open scoped Real

noncomputable section

namespace RSInt

/-! ## 1. A generic parametric-holomorphy lemma -/

theorem abs_log_le_of_ge {r m : ℝ} (hm : 0 < m) (hr : m ≤ r) : |Real.log r| ≤ r + |Real.log m| := by
  have hr0 : 0 < r := lt_of_lt_of_le hm hr
  rcases le_total 1 r with h | h
  · rw [abs_of_nonneg (Real.log_nonneg h)]
    have := Real.log_le_sub_one_of_pos hr0
    linarith [abs_nonneg (Real.log m)]
  · rw [abs_of_nonpos (Real.log_nonpos hr0.le h)]
    have h1 : Real.log m ≤ Real.log r := Real.log_le_log hm hr
    linarith [neg_abs_le (Real.log m)]

theorem norm_log_le {x : ℂ} {m : ℝ} (hm : 0 < m) (hx : m ≤ ‖x‖) :
    ‖Complex.log x‖ ≤ ‖x‖ + |Real.log m| + π := by
  have h1 := Complex.norm_le_abs_re_add_abs_im (Complex.log x)
  rw [Complex.log_re, Complex.log_im] at h1
  have h2 := abs_log_le_of_ge hm hx
  have h3 := Complex.abs_arg_le_pi x
  linarith



/-! ## 2. The two Riemann-Siegel line integrals are entire in `s` -/



















/-! ## 3. The chi factor -/















end RSInt

end

/-  RS_Entire.lean -- lane RS, ANDURIL brick B2 (the Riemann-Siegel integral), part 5:
    holomorphy in `s` of the two Riemann-Siegel line integrals, and the chi factor.
    Mathlib-only (imports `RS_Fold`).

    ## Contents (no `sorry`, no `native_decide`, no new axioms)

      * `differentiable_integral_cpow` : a generic parametric-holomorphy lemma:
            s |-> int W(v) X(v)^s dv   is entire
        for continuous W with a Gaussian tail and a continuous line X in the slit plane with
        m <= |X v| <= alpha + beta |v|.
      * `differentiable_rsA`, `differentiable_rsB` : s |-> lineUp c (rsG x^(-s)) and
        s |-> lineDn c (rsH x^(s-1)) are entire for every c > 0 that is not an integer.
      * `rsChi s = pi^(s - 1/2) Gamma((1-s)/2) / Gamma(s/2)`, holomorphic off {1, 3, 5, ...}
        (`differentiableAt_rsChi`), with the Gamma-function identity
            rsChi s * Gamma s * (2 cos(pi s / 2)) = (2 pi)^s     (Re s > 0)
        (`rsChi_mul_Gamma_cos`, reflection + duplication).

    conjecture1_proved = False.
-/


open Complex MeasureTheory Filter Topology Set
open scoped Real

noncomputable section

section
namespace RSInt
end RSInt
open RSInt

/-! ## 1. A generic parametric-holomorphy lemma -/






theorem solution {W X : ℝ → ℂ} (hW : Continuous W) (hX : Continuous X)
    (hXs : ∀ v, X v ∈ slitPlane) {m : ℝ} (hm : 0 < m) (hXm : ∀ v, m ≤ ‖X v‖)
    {α β : ℝ} (hXb : ∀ v, ‖X v‖ ≤ α + β * |v|)
    {C a b : ℝ} (ha : 0 < a) (hWb : ∀ v, 1 ≤ |v| → ‖W v‖ ≤ C * Real.exp (-a * v ^ 2 + b * |v|)) :
    Differentiable ℂ (fun s : ℂ => ∫ v : ℝ, W v * X v ^ s) := by
  intro s₀
  have hX0 : ∀ v, X v ≠ 0 := fun v => slitPlane_ne_zero (hXs v)
  set K : ℝ := ‖s₀‖ + 2 with hK
  have hK0 : 0 ≤ K := by positivity
  set L : ℝ → ℝ := fun v => α + β * |v| + |Real.log m| + π with hL
  have hlogL : ∀ v, ‖Complex.log (X v)‖ ≤ L v := by
    intro v
    have := norm_log_le hm (hXm v)
    have := hXb v
    simp only [hL]; linarith
  -- the dominating function
  set bound : ℝ → ℝ := fun v => ‖W v‖ * Real.exp (K * L v) with hbound
  have hcpow_le : ∀ v (s : ℂ), s ∈ Metric.ball s₀ 1 → ‖X v ^ s‖ ≤ Real.exp ((K - 1) * L v) := by
    intro v s hs
    rw [Complex.cpow_def_of_ne_zero (hX0 v)]
    refine (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr ?_)
    rw [norm_mul]
    have h1 : ‖s‖ ≤ ‖s₀‖ + 1 := by
      have := Metric.mem_ball.mp hs
      rw [dist_eq_norm] at this
      have := norm_sub_norm_le s s₀
      linarith
    have h2 := hlogL v
    have hL0 : 0 ≤ L v := le_trans (norm_nonneg _) h2
    calc ‖Complex.log (X v)‖ * ‖s‖ ≤ L v * (‖s₀‖ + 1) :=
          mul_le_mul h2 h1 (norm_nonneg _) hL0
      _ = (K - 1) * L v := by simp only [hK]; ring
  have hbound_int : Integrable bound := by
    have hLc : Continuous L := by simp only [hL]; fun_prop
    refine integrable_of_continuous_of_tail (f := fun v => (bound v : ℂ))
      (by simp only [hbound]; fun_prop) (a := a) (R := 1)
      (C := C * Real.exp (K * (|α| + |Real.log m| + π)))
      (b := b + K * |β|) ha (fun v hv => ?_) |>.norm.congr (Eventually.of_forall fun v => ?_)
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      simp only [hbound]
      have h1 := hWb v hv
      have h2 : K * L v ≤ K * (|α| + |Real.log m| + π) + K * |β| * |v| := by
        simp only [hL]
        have : α + β * |v| + |Real.log m| + π ≤ |α| + |Real.log m| + π + |β| * |v| := by
          have := le_abs_self α
          have : β * |v| ≤ |β| * |v| := mul_le_mul_of_nonneg_right (le_abs_self β) (abs_nonneg v)
          linarith
        nlinarith
      calc ‖W v‖ * Real.exp (K * L v)
          ≤ C * Real.exp (-a * v ^ 2 + b * |v|) *
              Real.exp (K * (|α| + |Real.log m| + π) + K * |β| * |v|) :=
            mul_le_mul h1 (Real.exp_le_exp.mpr h2) (Real.exp_pos _).le
              (le_trans (norm_nonneg _) h1)
        _ = C * Real.exp (K * (|α| + |Real.log m| + π)) *
              Real.exp (-a * v ^ 2 + (b + K * |β|) * |v|) := by
            have e1 : ∀ p q : ℝ, C * Real.exp p * Real.exp q = C * Real.exp (p + q) := by
              intro p q; rw [Real.exp_add]; ring
            rw [e1, e1]; congr 2; ring
    · simp only [Complex.norm_real, Real.norm_eq_abs, hbound]
      exact abs_of_nonneg (by positivity)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun (s : ℂ) (v : ℝ) => W v * X v ^ s)
    (F' := fun (s : ℂ) (v : ℝ) => W v * (X v ^ s * Complex.log (X v)))
    (x₀ := s₀) (bound := bound) (Metric.ball_mem_nhds s₀ one_pos)
    (Eventually.of_forall fun s => ?_) ?_ ?_ ?_ hbound_int ?_
  · exact key.2.differentiableAt
  · -- measurability
    have : Continuous (fun v => X v ^ s) := by
      rw [continuous_iff_continuousAt]; intro v
      exact (continuousAt_cpow_const (hXs v)).comp hX.continuousAt
    exact (hW.mul this).aestronglyMeasurable
  · -- integrability at s₀
    refine hbound_int.mono' ?_ (Eventually.of_forall fun v => ?_)
    · have : Continuous (fun v => X v ^ s₀) := by
        rw [continuous_iff_continuousAt]; intro v
        exact (continuousAt_cpow_const (hXs v)).comp hX.continuousAt
      exact (hW.mul this).aestronglyMeasurable
    · rw [norm_mul]
      have h1 := hcpow_le v s₀ (Metric.mem_ball_self one_pos)
      have hL0 : 0 ≤ L v := le_trans (norm_nonneg _) (hlogL v)
      have h2 : Real.exp ((K - 1) * L v) ≤ Real.exp (K * L v) :=
        Real.exp_le_exp.mpr (by nlinarith)
      exact mul_le_mul_of_nonneg_left (h1.trans h2) (norm_nonneg _)
  · -- measurability of the derivative
    have h1 : Continuous (fun v => X v ^ s₀) := by
      rw [continuous_iff_continuousAt]; intro v
      exact (continuousAt_cpow_const (hXs v)).comp hX.continuousAt
    have h2 : Continuous (fun v => Complex.log (X v)) := by
      rw [continuous_iff_continuousAt]; intro v
      exact (continuousAt_clog (hXs v)).comp hX.continuousAt
    exact (hW.mul (h1.mul h2)).aestronglyMeasurable
  · -- the bound on the derivative
    refine Eventually.of_forall fun v s hs => ?_
    rw [norm_mul, norm_mul]
    have h1 := hcpow_le v s hs
    have h2 := hlogL v
    have hL0 : 0 ≤ L v := le_trans (norm_nonneg _) h2
    have h3 : Real.exp ((K - 1) * L v) * L v ≤ Real.exp (K * L v) := by
      have h4 : L v ≤ Real.exp (L v) := by
        have := Real.add_one_le_exp (L v); linarith
      calc Real.exp ((K - 1) * L v) * L v ≤ Real.exp ((K - 1) * L v) * Real.exp (L v) :=
            mul_le_mul_of_nonneg_left h4 (Real.exp_pos _).le
        _ = Real.exp (K * L v) := by rw [← Real.exp_add]; congr 1; ring
    calc ‖W v‖ * (‖X v ^ s‖ * ‖Complex.log (X v)‖)
        ≤ ‖W v‖ * (Real.exp ((K - 1) * L v) * L v) := by
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
          exact mul_le_mul h1 h2 (norm_nonneg _) (Real.exp_pos _).le
      _ ≤ ‖W v‖ * Real.exp (K * L v) := mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
  · -- the derivative
    refine Eventually.of_forall fun v s _ => ?_
    exact ((Complex.hasStrictDerivAt_const_cpow (Or.inl (hX0 v))).hasDerivAt).const_mul (W v)
