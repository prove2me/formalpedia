-- Prove2me | solution 1 for ZudilinZeta.complex_stirling_right_half_plane
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-01T21:53:43.915094+00:00
-- url     : https://prove2.me/submissions/646da70b-e897-43b3-9e2f-065d0f51760e

import Mathlib
import Definitions.Def_Zeta23_GammaFacts_StirlingVert
import Theorems.Thm_Zeta23_DigammaSeries_hasSum_digamma_series
import Theorems.Thm_Zeta23_StirlingVert_partial_sum_eq
import Theorems.Thm_Zeta23_StirlingVert_tendsto_harmonic_sub_clog
import Theorems.Thm_Zeta23_StirlingVert_integral_inv_add_eq

/-
The interval-integral argument below adapts the accepted Prove2Me proof
43a60f86-918c-450e-8c6f-198ececaf10b, Copyright (c) 2026 Anthropic, PBC,
released under Apache 2.0. Here the denominator is bounded by its real part,
so the estimates apply throughout the right half-plane.
-/

set_option autoImplicit false

noncomputable section
open Complex Filter Topology MeasureTheory intervalIntegral Set
open Zeta23.StirlingVert

namespace ZudilinZeta.GammaEstimates

lemma add_ne_zero {w : ℂ} (hw : 0 < w.re) {x : ℝ} (hx : 0 ≤ x) :
    (x : ℂ) + w ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp only [Complex.add_re, Complex.ofReal_re, Complex.zero_re] at this
  linarith

lemma re_add_le_norm (w : ℂ) (x : ℝ) : x + w.re ≤ ‖(x : ℂ) + w‖ := by
  simpa using Complex.re_le_norm ((x : ℂ) + w)

lemma norm_eps_le_re {w : ℂ} (hw : 0 < w.re) {m : ℝ} (hm : 0 ≤ m) :
    ‖eps w m‖ ≤ 1 / (3 * (m + w.re) ^ 3) := by
  have hmw := add_ne_zero hw hm
  have hpos : 0 < m + w.re := by positivity
  unfold eps
  calc
    ‖∫ x in m..m + 1, ((x - m : ℝ) : ℂ) ^ 2 /
        (((m : ℂ) + w) ^ 2 * ((x : ℂ) + w))‖
      ≤ ∫ x in m..m + 1, ‖((x - m : ℝ) : ℂ) ^ 2 /
        (((m : ℂ) + w) ^ 2 * ((x : ℂ) + w))‖ :=
      intervalIntegral.norm_integral_le_integral_norm (by linarith)
    _ ≤ ∫ x in m..m + 1, (x - m) ^ 2 / (m + w.re) ^ 3 := by
      apply intervalIntegral.integral_mono_on (by linarith)
      · refine (ContinuousOn.intervalIntegrable ?_).norm
        apply ContinuousOn.div (by fun_prop) (by fun_prop)
        intro x hx
        rw [uIcc_of_le (by linarith)] at hx
        exact mul_ne_zero (pow_ne_zero _ hmw) (add_ne_zero hw (by linarith [hx.1]))
      · exact (by fun_prop : Continuous fun x : ℝ =>
          (x - m) ^ 2 / (m + w.re) ^ 3).intervalIntegrable _ _
      · intro x hx
        have hxw : m + w.re ≤ ‖(x : ℂ) + w‖ :=
          le_trans (by linarith [hx.1]) (re_add_le_norm w x)
        rw [norm_div, norm_mul, norm_pow, norm_pow, Complex.norm_real,
          Real.norm_eq_abs, sq_abs]
        apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
        calc (m + w.re) ^ 3 = (m + w.re) ^ 2 * (m + w.re) := by ring
          _ ≤ ‖(m : ℂ) + w‖ ^ 2 * ‖(x : ℂ) + w‖ := by
            gcongr
            exact re_add_le_norm w m
    _ = 1 / (3 * (m + w.re) ^ 3) := by
      rw [intervalIntegral.integral_div,
        intervalIntegral.integral_comp_sub_right (fun u : ℝ => u ^ 2) m]
      simp only [sub_self, add_sub_cancel_left, integral_pow]
      norm_num
      ring

lemma norm_rho_le_re {w : ℂ} (hw : 0 < w.re) (n : ℕ) :
    ‖rho w n‖ ≤ 1 / ((n : ℝ) + 1 + w.re) ^ 3 := by
  have h1 : (n : ℝ) + 1 + w.re ≤ ‖(n : ℂ) + 1 + w‖ := by
    simpa using Complex.re_le_norm ((n : ℂ) + 1 + w)
  have h2 : (n : ℝ) + 1 + w.re ≤ ‖(n : ℂ) + 2 + w‖ := by
    have := Complex.re_le_norm ((n : ℂ) + 2 + w)
    simp only [Complex.add_re, Complex.natCast_re, Complex.re_ofNat] at this
    linarith
  unfold rho
  rw [norm_div, norm_one, norm_mul, norm_pow]
  apply div_le_div_of_nonneg_left zero_le_one (by positivity)
  calc ((n : ℝ) + 1 + w.re) ^ 3 =
      ((n : ℝ) + 1 + w.re) ^ 2 * ((n : ℝ) + 1 + w.re) := by ring
    _ ≤ ‖(n : ℂ) + 1 + w‖ ^ 2 * ‖(n : ℂ) + 2 + w‖ := by gcongr

lemma summable_reciprocal_square {x : ℝ} (hx : 0 < x) :
    Summable (fun n : ℕ => 1 / ((n : ℝ) + 1 + x) ^ 2) := by
  have hs : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) := by
    have := Real.summable_one_div_nat_pow.mpr one_lt_two
    exact_mod_cast (summable_nat_add_iff 1).mpr this
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hs
  apply div_le_div_of_nonneg_left zero_le_one (by positivity)
  exact pow_le_pow_left₀ (by positivity) (by linarith) 2

lemma sum_reciprocal_square_le {x : ℝ} (hx : 0 < x) (N : ℕ) :
    ∑ n ∈ Finset.range N, 1 / ((n : ℝ) + 1 + x) ^ 2 ≤ 1 / x := by
  have hstep (n : ℕ) : 1 / ((n : ℝ) + 1 + x) ^ 2 ≤
      1 / ((n : ℝ) + x) - 1 / ((n : ℝ) + 1 + x) := by
    have hn : 0 < (n : ℝ) + x := by positivity
    have hn1 : 0 < (n : ℝ) + 1 + x := by positivity
    rw [div_sub_div _ _ (ne_of_gt hn) (ne_of_gt hn1)]
    ring_nf
    field_simp
    nlinarith
  calc
    ∑ n ∈ Finset.range N, 1 / ((n : ℝ) + 1 + x) ^ 2
      ≤ ∑ n ∈ Finset.range N,
        (1 / ((n : ℝ) + x) - 1 / ((n : ℝ) + 1 + x)) :=
      Finset.sum_le_sum fun n _ => hstep n
    _ = 1 / x - 1 / ((N : ℝ) + x) := by
      convert Finset.sum_range_sub' (fun n : ℕ => 1 / ((n : ℝ) + x)) N using 1 <;>
        simp [Nat.cast_add, Nat.cast_one]
    _ ≤ 1 / x := sub_le_self _ (by positivity)

lemma tsum_reciprocal_square_le {x : ℝ} (hx : 0 < x) :
    ∑' n : ℕ, 1 / ((n : ℝ) + 1 + x) ^ 2 ≤ 1 / x :=
  Real.tsum_le_of_sum_range_le (fun n => by positivity) (sum_reciprocal_square_le hx)

lemma reciprocal_cube_le {x : ℝ} (hx : 0 < x) (n : ℕ) :
    1 / ((n : ℝ) + 1 + x) ^ 3 ≤
      (1 / x) * (1 / ((n : ℝ) + 1 + x) ^ 2) := by
  have hn : 0 < (n : ℝ) + 1 + x := by positivity
  calc
    1 / ((n : ℝ) + 1 + x) ^ 3 =
      (1 / ((n : ℝ) + 1 + x)) * (1 / ((n : ℝ) + 1 + x) ^ 2) := by
        field_simp
    _ ≤ (1 / x) * (1 / ((n : ℝ) + 1 + x) ^ 2) := by
      gcongr
      linarith

lemma summable_norm_rho_re {w : ℂ} (hw : 0 < w.re) :
    Summable (fun n => ‖rho w n‖) :=
  Summable.of_nonneg_of_le (fun n => norm_nonneg _)
    (fun n => (norm_rho_le_re hw n).trans (reciprocal_cube_le hw n))
    ((summable_reciprocal_square hw).mul_left _)

lemma norm_eps_natp1_le_re {w : ℂ} (hw : 0 < w.re) (n : ℕ) :
    ‖eps w ((n : ℝ) + 1)‖ ≤
      (1 / (3 * w.re)) * (1 / ((n : ℝ) + 1 + w.re) ^ 2) := by
  calc
    ‖eps w ((n : ℝ) + 1)‖ ≤ 1 / (3 * ((n : ℝ) + 1 + w.re) ^ 3) :=
      norm_eps_le_re hw (by positivity)
    _ = (1 / 3) * (1 / ((n : ℝ) + 1 + w.re) ^ 3) := by rw [one_div_mul_one_div]
    _ ≤ (1 / 3) * ((1 / w.re) * (1 / ((n : ℝ) + 1 + w.re) ^ 2)) :=
      mul_le_mul_of_nonneg_left (reciprocal_cube_le hw n) (by positivity)
    _ = _ := by ring

lemma summable_norm_eps_re {w : ℂ} (hw : 0 < w.re) :
    Summable (fun n : ℕ => ‖eps w ((n : ℝ) + 1)‖) :=
  Summable.of_nonneg_of_le (fun n => norm_nonneg _) (norm_eps_natp1_le_re hw)
    ((summable_reciprocal_square hw).mul_left _)

lemma norm_tsum_rho_le_re {w : ℂ} (hw : 0 < w.re) :
    ‖∑' n, rho w n‖ ≤ 1 / w.re ^ 2 := by
  calc
    ‖∑' n, rho w n‖ ≤ ∑' n, ‖rho w n‖ :=
      norm_tsum_le_tsum_norm (summable_norm_rho_re hw)
    _ ≤ ∑' n : ℕ, (1 / w.re) * (1 / ((n : ℝ) + 1 + w.re) ^ 2) :=
      Summable.tsum_le_tsum (fun n =>
        (norm_rho_le_re hw n).trans (reciprocal_cube_le hw n))
        (summable_norm_rho_re hw) ((summable_reciprocal_square hw).mul_left _)
    _ = (1 / w.re) * ∑' n : ℕ, 1 / ((n : ℝ) + 1 + w.re) ^ 2 := tsum_mul_left
    _ ≤ (1 / w.re) * (1 / w.re) := by
      exact mul_le_mul_of_nonneg_left (tsum_reciprocal_square_le hw) (by positivity)
    _ = _ := by ring

lemma norm_tsum_eps_le_re {w : ℂ} (hw : 0 < w.re) :
    ‖∑' n : ℕ, eps w ((n : ℝ) + 1)‖ ≤ 1 / (3 * w.re ^ 2) := by
  calc
    ‖∑' n : ℕ, eps w ((n : ℝ) + 1)‖ ≤ ∑' n : ℕ, ‖eps w ((n : ℝ) + 1)‖ :=
      norm_tsum_le_tsum_norm (summable_norm_eps_re hw)
    _ ≤ ∑' n : ℕ, (1 / (3 * w.re)) * (1 / ((n : ℝ) + 1 + w.re) ^ 2) :=
      Summable.tsum_le_tsum (norm_eps_natp1_le_re hw)
        (summable_norm_eps_re hw) ((summable_reciprocal_square hw).mul_left _)
    _ = (1 / (3 * w.re)) * ∑' n : ℕ, 1 / ((n : ℝ) + 1 + w.re) ^ 2 := tsum_mul_left
    _ ≤ (1 / (3 * w.re)) * (1 / w.re) := by
      exact mul_le_mul_of_nonneg_left (tsum_reciprocal_square_le hw) (by positivity)
    _ = _ := by ring

end ZudilinZeta.GammaEstimates
end

/-
The exact-identity and logarithm calculations adapt accepted Prove2Me proofs
4af605bc-c33d-45b4-b8fd-6321916b5279 and 9827dfcf-2988-442e-b5f3-b4c0e6850bf9,
Copyright (c) 2026 Anthropic, PBC, released under Apache 2.0.
The remainder bounds are replaced by bounds in the real part of the argument.
-/

set_option autoImplicit false
noncomputable section
open Complex Filter Topology MeasureTheory intervalIntegral Set
open Zeta23.StirlingVert
namespace ZudilinZeta.GammaEstimates

lemma tendsto_inv_natp1 {w : ℂ} (hw : 0 < w.re) :
    Tendsto (fun N : ℕ => ((N : ℂ) + 1 + w)⁻¹) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    tendsto_one_div_add_atTop_nhds_zero_nat (fun N => norm_nonneg _) (fun N => ?_)
  rw [norm_inv, inv_eq_one_div]
  apply one_div_le_one_div_of_le (by positivity)
  have := Complex.re_le_norm ((N : ℂ) + 1 + w)
  simp at this
  linarith

lemma digamma_eq_re {w : ℂ} (hw : 0 < w.re) (hmem : w ∈ Complex.integerComplement) :
    Complex.digamma w = Complex.log (1 + w) - 1 / w - (1 / 2 : ℂ) * (1 + w)⁻¹
      - (1 / 2 : ℂ) * (∑' n, rho w n) + ∑' n : ℕ, eps w ((n : ℝ) + 1) := by
  have hL := (Zeta23.DigammaSeries.hasSum_digamma_series hmem).tendsto_sum_nat
  -- the same partial sums, rearranged
  have hR : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, (1 / ((n : ℂ) + 1) - 1 / (w + n + 1)))
      atTop (𝓝 ((Real.eulerMascheroniConstant : ℂ) + Complex.log (1 + w)
        - (1 / 2 : ℂ) * ((1 + w)⁻¹ - 0 + ∑' n, rho w n) + ∑' n : ℕ, eps w ((n : ℝ) + 1))) := by
    have e : ∀ N : ℕ, ∑ n ∈ Finset.range N, (1 / ((n : ℂ) + 1) - 1 / (w + n + 1))
        = ((∑ n ∈ Finset.range N, 1 / ((n : ℂ) + 1)) - Complex.log ((N : ℂ) + 1 + w))
          + Complex.log (1 + w)
          - (1 / 2 : ℂ) * ((1 + w)⁻¹ - ((N : ℂ) + 1 + w)⁻¹ + ∑ n ∈ Finset.range N, rho w n)
          + ∑ n ∈ Finset.range N, eps w ((n : ℝ) + 1) := by
      intro N
      rw [partial_sum_eq hw N]
      push_cast
      ring
    simp_rw [e]
    refine (((tendsto_harmonic_sub_clog hw).add tendsto_const_nhds).sub
      (((tendsto_const_nhds.sub (tendsto_inv_natp1 hw)).add
        (summable_norm_rho_re hw).of_norm.hasSum.tendsto_sum_nat).const_mul _)).add
      (summable_norm_eps_re hw).of_norm.hasSum.tendsto_sum_nat
  have := tendsto_nhds_unique hL hR
  rw [sub_zero] at this
  linear_combination this

lemma log_one_add_sub_log {w : ℂ} (hw : 0 < w.re) :
    Complex.log (1 + w) - Complex.log w = w⁻¹ - (1 / 2 : ℂ) / w ^ 2 + eps w 0 := by
  have hd {x : ℝ} (hx : 0 ≤ x) :
      HasDerivAt (fun y : ℝ => Complex.log ((y : ℂ) + w)) (((x : ℂ) + w)⁻¹) x := by
    have hz : (x : ℂ) + w ∈ Complex.slitPlane :=
      Complex.mem_slitPlane_iff.mpr (Or.inl (by simp; positivity))
    have h1 := (Complex.hasDerivAt_log hz).comp (x : ℂ)
      ((hasDerivAt_id (x : ℂ)).add_const w)
    simpa [Function.comp_def] using h1.comp_ofReal
  have hcont : ContinuousOn (fun x : ℝ => ((x : ℂ) + w)⁻¹) (uIcc 0 1) := by
    apply ContinuousOn.inv₀ (by fun_prop)
    intro x hx
    rw [uIcc_of_le zero_le_one] at hx
    exact add_ne_zero hw hx.1
  have h1 := integral_inv_add_eq hw (m := 0) le_rfl
  have h2 := integral_eq_sub_of_hasDerivAt (a := 0) (b := 1)
    (f := fun y : ℝ => Complex.log ((y : ℂ) + w))
    (fun x hx => hd (by simpa [uIcc_of_le zero_le_one] using hx.1))
    hcont.intervalIntegrable
  norm_num at h1 h2
  rw [h2] at h1
  simpa using h1

lemma digamma_stirling_of_noninteger {w : ℂ} (hw : 1 ≤ w.re)
    (hmem : w ∈ Complex.integerComplement) :
    ‖Complex.digamma w - Complex.log w + (1 / 2 : ℂ) / w‖ ≤ 2 / w.re ^ 2 := by
  have hwpos : 0 < w.re := by linarith
  have hw0 : w ≠ 0 := by intro h; norm_num [h] at hw
  have h1w : 1 + w ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hid := digamma_eq_re hwpos hmem
  have hlog := log_one_add_sub_log hwpos
  have key : Complex.digamma w - Complex.log w + (1 / 2 : ℂ) / w
      = -(1 / 2 : ℂ) / (w ^ 2 * (1 + w)) + eps w 0
        - (1 / 2 : ℂ) * (∑' n, rho w n) + ∑' n : ℕ, eps w ((n : ℝ) + 1) := by
    rw [hid, show Complex.log (1 + w) = Complex.log w +
      (w⁻¹ - (1 / 2 : ℂ) / w ^ 2 + eps w 0) by rw [← hlog]; ring]
    field_simp
    ring
  have b1 : ‖-(1 / 2 : ℂ) / (w ^ 2 * (1 + w))‖ ≤ (1 / 2) / w.re ^ 2 := by
    rw [norm_div, norm_neg, norm_mul, norm_pow,
      show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num]
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    have h1 : 1 ≤ ‖1 + w‖ := by
      have := Complex.re_le_norm (1 + w)
      simp at this
      linarith
    calc w.re ^ 2 = w.re ^ 2 * 1 := (mul_one _).symm
      _ ≤ ‖w‖ ^ 2 * ‖1 + w‖ := by gcongr; exact Complex.re_le_norm w
  have b2 : ‖eps w 0‖ ≤ (1 / 3) / w.re ^ 2 := by
    calc ‖eps w 0‖ ≤ 1 / (3 * w.re ^ 3) := by
          simpa using norm_eps_le_re hwpos (m := 0) le_rfl
      _ ≤ (1 / 3) / w.re ^ 2 := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [mul_le_mul_of_nonneg_right hw (sq_nonneg w.re)]
  have b3 : ‖(1 / 2 : ℂ) * ∑' n, rho w n‖ ≤ (1 / 2) / w.re ^ 2 := by
    rw [norm_mul, show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num]
    calc (1 / 2) * ‖∑' n, rho w n‖ ≤ (1 / 2) * (1 / w.re ^ 2) :=
          mul_le_mul_of_nonneg_left (norm_tsum_rho_le_re hwpos) (by norm_num)
      _ = _ := by ring
  have b4 := norm_tsum_eps_le_re hwpos
  rw [key]
  calc
    ‖-(1 / 2 : ℂ) / (w ^ 2 * (1 + w)) + eps w 0 -
        (1 / 2 : ℂ) * ∑' n, rho w n + ∑' n : ℕ, eps w ((n : ℝ) + 1)‖
      ≤ ‖-(1 / 2 : ℂ) / (w ^ 2 * (1 + w))‖ + ‖eps w 0‖ +
        ‖(1 / 2 : ℂ) * ∑' n, rho w n‖ + ‖∑' n : ℕ, eps w ((n : ℝ) + 1)‖ := by
        have s1 := norm_add_le
          (-(1 / 2 : ℂ) / (w ^ 2 * (1 + w)) + eps w 0 - (1 / 2 : ℂ) * ∑' n, rho w n)
          (∑' n : ℕ, eps w ((n : ℝ) + 1))
        have s2 := norm_sub_le (-(1 / 2 : ℂ) / (w ^ 2 * (1 + w)) + eps w 0)
          ((1 / 2 : ℂ) * ∑' n, rho w n)
        have s3 := norm_add_le (-(1 / 2 : ℂ) / (w ^ 2 * (1 + w))) (eps w 0)
        linarith
    _ ≤ (1 / 2) / w.re ^ 2 + (1 / 3) / w.re ^ 2 +
        (1 / 2) / w.re ^ 2 + 1 / (3 * w.re ^ 2) := by gcongr
    _ ≤ 2 / w.re ^ 2 := by
      rw [show (1 / 2) / w.re ^ 2 + (1 / 3) / w.re ^ 2 +
        (1 / 2) / w.re ^ 2 + 1 / (3 * w.re ^ 2) = (5 / 3) / w.re ^ 2 by ring]
      exact div_le_div_of_nonneg_right (by norm_num) (sq_nonneg w.re)

lemma continuousAt_digamma_right {w : ℂ} (hw : 0 < w.re) :
    ContinuousAt Complex.digamma w := by
  have hgamma : AnalyticAt ℂ Complex.Gamma w := by
    apply DifferentiableOn.analyticAt (s := {z : ℂ | 0 < z.re})
      (fun z hz => (Complex.differentiableAt_Gamma z ?_).differentiableWithinAt)
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hw)
    intro m hm
    have := congrArg Complex.re hm
    simp at this
    change 0 < z.re at hz
    have : (0 : ℝ) ≤ m := by positivity
    linarith
  exact (hgamma.deriv.continuousAt.div hgamma.continuousAt
    (Complex.Gamma_ne_zero_of_re_pos hw) : ContinuousAt (logDeriv Complex.Gamma) w)

lemma digamma_stirling_right {w : ℂ} (hw : 1 ≤ w.re) :
    ‖Complex.digamma w - Complex.log w + (1 / 2 : ℂ) / w‖ ≤ 2 / w.re ^ 2 := by
  have hwpos : 0 < w.re := by linarith
  have hnmem {z : ℂ} (hz : z.im ≠ 0) : z ∈ Complex.integerComplement := by
    rintro ⟨k, hk⟩
    have := congrArg Complex.im hk
    simp at this
    exact hz this.symm
  by_cases him : w.im = 0
  · let u : ℕ → ℂ := fun n => w + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * I
    have hu : Tendsto u atTop (𝓝 w) := by
      have h := ((Complex.continuous_ofReal.tendsto 0).comp
        tendsto_one_div_add_atTop_nhds_zero_nat).mul_const I
      simpa [u] using tendsto_const_nhds.add h
    have hure (n : ℕ) : (u n).re = w.re := by simp [u]
    have humem (n : ℕ) : u n ∈ Complex.integerComplement := by
      apply hnmem
      have : 0 < (u n).im := by
        simp only [u, Complex.add_im, him, Complex.mul_im, Complex.ofReal_re,
          Complex.I_im, Complex.ofReal_im, Complex.I_re, mul_one, zero_mul,
          add_zero, zero_add]
        positivity
      exact ne_of_gt this
    have hcont : ContinuousAt (fun z : ℂ =>
        ‖Complex.digamma z - Complex.log z + (1 / 2 : ℂ) / z‖) w := by
      apply ContinuousAt.norm
      apply ContinuousAt.add
      · exact (continuousAt_digamma_right hwpos).sub
          (continuousAt_clog (Complex.mem_slitPlane_iff.mpr (Or.inl hwpos)))
      · exact continuousAt_const.div continuousAt_id (by intro h; norm_num [h] at hw)
    apply le_of_tendsto (hcont.tendsto.comp hu)
    filter_upwards [] with n
    convert! digamma_stirling_of_noninteger
      (w := u n) (by simpa only [hure] using hw) (humem n) using 1 <;>
      simp only [Function.comp_apply, hure]
  · exact digamma_stirling_of_noninteger hw (hnmem him)

end ZudilinZeta.GammaEstimates
end

set_option autoImplicit false
noncomputable section
open Complex Filter Topology MeasureTheory intervalIntegral Set

namespace ZudilinZeta.GammaEstimates

def gammaExponent (w : ℂ) : ℂ := (w + 1 / 2) * Complex.log w - w

def normalizedGamma (w : ℂ) : ℂ :=
  Complex.Gamma (w + 1) * Complex.exp (-gammaExponent w) / Real.sqrt (2 * Real.pi)

def gammaError (w : ℂ) : ℂ := Complex.digamma w - Complex.log w + (1 / 2 : ℂ) / w

lemma norm_gammaError_le {w : ℂ} (hw : 1 ≤ w.re) :
    ‖gammaError w‖ ≤ 2 / w.re ^ 2 := digamma_stirling_right hw

lemma continuousAt_gammaError {w : ℂ} (hw : 0 < w.re) :
    ContinuousAt gammaError w := by
  have hw0 : w ≠ 0 := by intro h; simpa [h] using hw
  exact ((continuousAt_digamma_right hw).sub
    (continuousAt_clog (Complex.mem_slitPlane_iff.mpr (Or.inl hw)))).add
    (continuousAt_const.div continuousAt_id hw0)

lemma normalizedGamma_ne_zero {w : ℂ} (hw : 0 < w.re) : normalizedGamma w ≠ 0 := by
  apply div_ne_zero
  · exact mul_ne_zero (Complex.Gamma_ne_zero_of_re_pos (by simpa using (by linarith : 0 < w.re + 1)))
      (Complex.exp_ne_zero _)
  · exact Complex.ofReal_ne_zero.mpr (by positivity)

lemma hasDerivAt_gammaExponent {w : ℂ} (hw : 0 < w.re) :
    HasDerivAt gammaExponent (Complex.log w + (1 / 2 : ℂ) / w) w := by
  have hw0 : w ≠ 0 := by intro h; simpa [h] using hw
  have h := (((hasDerivAt_id w).add_const (1 / 2 : ℂ)).fun_mul
    (Complex.hasDerivAt_log (Complex.mem_slitPlane_iff.mpr (Or.inl hw)))).sub (hasDerivAt_id w)
  convert! h using 1
  dsimp
  field_simp
  ring

lemma hasDerivAt_normalizedGamma {w : ℂ} (hw : 0 < w.re) :
    HasDerivAt normalizedGamma (normalizedGamma w * gammaError w) w := by
  have hnot (m : ℕ) : w ≠ -(m : ℂ) := by
    intro h
    have := congrArg Complex.re h
    simp at this
    have : (0 : ℝ) ≤ m := by positivity
    linarith
  have hnot1 (m : ℕ) : w + 1 ≠ -(m : ℂ) := by
    intro h
    have := congrArg Complex.re h
    simp at this
    have : (0 : ℝ) ≤ m := by positivity
    linarith
  have hG : HasDerivAt (fun z : ℂ => Complex.Gamma (z + 1))
      (Complex.Gamma (w + 1) * Complex.digamma (w + 1)) w := by
    have h := (Complex.differentiableAt_Gamma (w + 1) hnot1).hasDerivAt.comp w
      ((hasDerivAt_id w).add_const 1)
    convert! h using 1
    simp only [mul_one]
    rw [Complex.digamma_def, logDeriv_apply]
    field_simp [Complex.Gamma_ne_zero hnot1]
  have he := ((hasDerivAt_gammaExponent hw).neg).cexp
  have hd := (hG.fun_mul he).div_const (Real.sqrt (2 * Real.pi) : ℂ)
  convert! hd using 1
  dsimp [normalizedGamma, gammaError]
  rw [Complex.digamma_apply_add_one w hnot]
  ring

lemma exp_gammaExponent_nat (n : ℕ) (hn : n ≠ 0) :
    Complex.exp (gammaExponent n) =
      ((Real.sqrt (n : ℝ) * ((n : ℝ) / Real.exp 1) ^ n : ℝ) : ℂ) := by
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hlog : Complex.log (n : ℂ) = (Real.log (n : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_natCast] using (Complex.ofReal_log hnpos.le).symm
  have he : Real.exp (((n : ℝ) + 1 / 2) * Real.log n - n) =
      Real.sqrt n * ((n : ℝ) / Real.exp 1) ^ n := by
    rw [show ((n : ℝ) + 1 / 2) * Real.log n - n =
      Real.log n / 2 + (n : ℝ) * (Real.log n - 1) by ring,
      Real.exp_add, Real.exp_half, Real.exp_log hnpos, Real.exp_nat_mul,
      Real.exp_sub, Real.exp_log hnpos]
  unfold gammaExponent
  rw [hlog]
  have hc := congrArg Complex.ofReal he
  rw [Complex.ofReal_exp] at hc
  push_cast at hc
  simpa only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_pow,
    Complex.ofReal_exp, Complex.ofReal_one, Complex.ofReal_natCast, hlog] using hc

lemma normalizedGamma_nat (n : ℕ) (hn : n ≠ 0) :
    normalizedGamma n =
      (((n.factorial : ℝ) / (Real.sqrt (2 * n * Real.pi) *
        ((n : ℝ) / Real.exp 1) ^ n) : ℝ) : ℂ) := by
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hden : Real.sqrt (2 * n * Real.pi) =
      Real.sqrt (2 * Real.pi) * Real.sqrt n := by
    rw [← Real.sqrt_mul (by positivity)]
    congr 1
    ring
  rw [normalizedGamma, Complex.Gamma_nat_eq_factorial, Complex.exp_neg,
    exp_gammaExponent_nat n hn, hden]
  push_cast
  ring

lemma tendsto_normalizedGamma_nat :
    Tendsto (fun n : ℕ => normalizedGamma n) atTop (𝓝 1) := by
  have hreal : Tendsto (fun n : ℕ =>
      (n.factorial : ℝ) / (Real.sqrt (2 * n * Real.pi) *
        ((n : ℝ) / Real.exp 1) ^ n)) atTop (𝓝 1) := by
    apply (Asymptotics.isEquivalent_iff_tendsto_one ?_).mp
      Stirling.factorial_isEquivalent_stirling
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    positivity
  have hc := (Complex.continuous_ofReal.tendsto 1).comp hreal
  apply Tendsto.congr' _ (by simpa only [Function.comp_def, Complex.ofReal_one] using hc)
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  exact (normalizedGamma_nat n (Nat.ne_of_gt hn)).symm

end ZudilinZeta.GammaEstimates
end

set_option autoImplicit false
noncomputable section
open Complex Filter Topology MeasureTheory intervalIntegral Set

namespace ZudilinZeta.GammaEstimates

lemma eq_mul_exp_integral {f g : ℝ → ℂ} {a b : ℝ}
    (hg : StronglyMeasurable g)
    (hgc : ∀ x ∈ uIcc a b, ContinuousAt g x)
    (hf : ∀ x ∈ uIcc a b, HasDerivAt f (f x * g x) x) :
    f b = f a * Complex.exp (∫ x in a..b, g x) := by
  have hgc' : ContinuousOn g (uIcc a b) := fun x hx => (hgc x hx).continuousWithinAt
  have hgi : IntervalIntegrable g volume a b := hgc'.intervalIntegrable
  have hder (x : ℝ) (hx : x ∈ uIcc a b) :
      HasDerivAt (fun y : ℝ => f y * Complex.exp (-(∫ t in a..y, g t))) 0 x := by
    have hi := integral_hasDerivAt_right (hgi.mono_set (uIcc_subset_uIcc_left hx))
      hg.stronglyMeasurableAtFilter (hgc x hx)
    convert! (hf x hx).fun_mul hi.neg.cexp using 1
    ring
  have h := integral_eq_sub_of_hasDerivAt hder (intervalIntegrable_const (c := (0 : ℂ)))
  simp only [intervalIntegral.integral_zero, integral_same, neg_zero, Complex.exp_zero, mul_one] at h
  have heq : f b * Complex.exp (-(∫ x in a..b, g x)) = f a := sub_eq_zero.mp h.symm
  calc
    f b = f b * (Complex.exp (-(∫ x in a..b, g x)) *
        Complex.exp (∫ x in a..b, g x)) := by
      rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
    _ = (f b * Complex.exp (-(∫ x in a..b, g x))) *
        Complex.exp (∫ x in a..b, g x) := by ring
    _ = _ := by rw [heq]

end ZudilinZeta.GammaEstimates
end

set_option autoImplicit false
noncomputable section
open Complex Filter Topology MeasureTheory intervalIntegral Set

namespace ZudilinZeta.GammaEstimates

lemma measurable_gammaError : Measurable gammaError :=
  (Complex.meromorphic_digamma.measurable.sub Complex.measurable_log).add
    (measurable_const.div measurable_id)

def horizontalGammaError (a b y : ℝ) : ℂ :=
  ∫ t in a..b, gammaError ((t : ℂ) + y * I)

def verticalGammaError (x y : ℝ) : ℂ :=
  ∫ t in (0 : ℝ)..y, I * gammaError ((x : ℂ) + t * I)

lemma normalizedGamma_horizontal {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) (y : ℝ) :
    normalizedGamma ((b : ℂ) + y * I) =
      normalizedGamma ((a : ℂ) + y * I) * Complex.exp (horizontalGammaError a b y) := by
  unfold horizontalGammaError
  apply eq_mul_exp_integral (f := fun t : ℝ => normalizedGamma ((t : ℂ) + y * I))
    (g := fun t : ℝ => gammaError ((t : ℂ) + y * I))
  · exact (measurable_gammaError.comp (by fun_prop)).stronglyMeasurable
  · intro t ht
    rw [uIcc_of_le hab] at ht
    exact (continuousAt_gammaError (by simp; linarith [ht.1])).comp
      (show ContinuousAt (fun t : ℝ => (t : ℂ) + y * I) t from by fun_prop)
  · intro t ht
    rw [uIcc_of_le hab] at ht
    have h := (hasDerivAt_normalizedGamma (w := (t : ℂ) + y * I)
      (by simp; linarith [ht.1])).comp (t : ℂ) ((hasDerivAt_id (t : ℂ)).add_const (y * I))
    convert! h.comp_ofReal using 1 <;> simp [Function.comp_def]

lemma normalizedGamma_vertical {x : ℝ} (hx : 1 ≤ x) (y : ℝ) :
    normalizedGamma ((x : ℂ) + y * I) =
      normalizedGamma (x : ℂ) * Complex.exp (verticalGammaError x y) := by
  have h := eq_mul_exp_integral (a := 0) (b := y)
    (f := fun t : ℝ => normalizedGamma ((x : ℂ) + t * I))
    (g := fun t : ℝ => I * gammaError ((x : ℂ) + t * I))
    ((measurable_gammaError.comp (by fun_prop)).const_mul I).stronglyMeasurable
    (fun t _ => ((continuousAt_gammaError (w := (x : ℂ) + t * I)
      (by simp; linarith)).comp (f := fun t : ℝ => (x : ℂ) + t * I)
        (by fun_prop)).const_mul I)
    (fun t _ => ?_)
  · simpa [verticalGammaError] using h
  · have h := (hasDerivAt_normalizedGamma (w := (x : ℂ) + t * I)
      (by simp; linarith)).comp (t : ℂ)
        (((hasDerivAt_id (t : ℂ)).mul_const I).const_add (x : ℂ))
    convert! h.comp_ofReal using 1 <;> ring

lemma norm_verticalGammaError_le {x : ℝ} (hx : 1 ≤ x) (y : ℝ) :
    ‖verticalGammaError x y‖ ≤ 2 * |y| / x ^ 2 := by
  calc
    ‖verticalGammaError x y‖ ≤ (2 / x ^ 2) * |y - 0| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro t _
      rw [norm_mul, Complex.norm_I, one_mul]
      simpa using norm_gammaError_le (w := (x : ℂ) + t * I) (by simpa using hx)
    _ = _ := by rw [sub_zero]; ring

lemma norm_horizontalGammaError_le {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) (y : ℝ) :
    ‖horizontalGammaError a b y‖ ≤ 2 / a := by
  have hcont : ContinuousOn (fun t : ℝ => 2 / t ^ 2) (uIcc a b) := by
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro t ht
    rw [uIcc_of_le hab] at ht
    apply pow_ne_zero
    linarith [ht.1]
  have hint : (∫ t in a..b, (2 : ℝ) / t ^ 2) = -2 / b - (-2 / a) := by
    apply integral_eq_sub_of_hasDerivAt _ hcont.intervalIntegrable
    intro t ht
    rw [uIcc_of_le hab] at ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    convert! ((hasDerivAt_id t).inv ht0).const_mul (-2 : ℝ) using 1 <;>
      simp only [id_eq, div_eq_mul_inv] <;> ring
  calc
    ‖horizontalGammaError a b y‖ ≤ ∫ t in a..b, (2 : ℝ) / t ^ 2 := by
      apply norm_integral_le_of_norm_le hab _ hcont.intervalIntegrable
      filter_upwards [] with t ht
      simpa using norm_gammaError_le (w := (t : ℂ) + y * I) (by simp; linarith [ht.1])
    _ = -2 / b - (-2 / a) := hint
    _ ≤ 2 / a := by
      have hb : 0 < b := by linarith
      have : 0 ≤ (2 : ℝ) / b := by positivity
      rw [neg_div, neg_div]
      linarith

lemma normalizedGamma_path {w : ℂ} (hw : 1 ≤ w.re) {x : ℝ} (hx : w.re ≤ x) :
    normalizedGamma w = normalizedGamma (x : ℂ) * Complex.exp
      (verticalGammaError x w.im - horizontalGammaError w.re x w.im) := by
  have hhor := normalizedGamma_horizontal hw hx w.im
  have hver := normalizedGamma_vertical (le_trans hw hx) w.im
  have hrep : (w.re : ℂ) + w.im * I = w := Complex.re_add_im w
  rw [hrep, hver] at hhor
  have hexp := Complex.exp_ne_zero (horizontalGammaError w.re x w.im)
  apply mul_right_cancel₀ hexp
  rw [← hhor]
  rw [mul_assoc, ← Complex.exp_add, sub_add_cancel]

lemma norm_gamma_path_error_le {w : ℂ} (hw : 1 ≤ w.re) {x : ℝ} (hx : w.re ≤ x) :
    ‖verticalGammaError x w.im - horizontalGammaError w.re x w.im‖ ≤
      2 / w.re + 2 * |w.im| / x ^ 2 := by
  have hv := norm_verticalGammaError_le (le_trans hw hx) w.im
  have hh := norm_horizontalGammaError_le hw hx w.im
  exact (norm_sub_le _ _).trans (by linarith)

end ZudilinZeta.GammaEstimates
end

set_option autoImplicit false
noncomputable section
open Complex Filter Topology

namespace ZudilinZeta.GammaEstimates

lemma norm_normalizedGamma_sub_one_le_exp {w : ℂ} (hw : 1 ≤ w.re) :
    ‖normalizedGamma w - 1‖ ≤ Real.exp (2 / w.re) - 1 := by
  let R : ℕ → ℝ := fun n => 2 / w.re + 2 * |w.im| / (n : ℝ) ^ 2
  have htail : Tendsto (fun n : ℕ => 2 * |w.im| / (n : ℝ) ^ 2) atTop (𝓝 0) := by
    simpa [div_pow, div_eq_mul_inv] using
      ((tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).pow 2).const_mul (2 * |w.im|)
  have hR : Tendsto R atTop (𝓝 (2 / w.re)) := by
    simpa [R] using tendsto_const_nhds.add htail
  have hG : Tendsto (fun n : ℕ => ‖normalizedGamma n - 1‖) atTop (𝓝 0) := by
    simpa using (tendsto_normalizedGamma_nat.sub_const 1).norm
  have hbound : ∀ᶠ n : ℕ in atTop, ‖normalizedGamma w - 1‖ ≤
      (‖normalizedGamma n - 1‖ + 1) * Real.exp (R n) - 1 := by
    have hn : ∀ᶠ n : ℕ in atTop, w.re ≤ (n : ℝ) :=
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).eventually
        (eventually_ge_atTop w.re)
    filter_upwards [hn] with n hn
    let E := verticalGammaError (n : ℝ) w.im - horizontalGammaError w.re (n : ℝ) w.im
    have hE : ‖E‖ ≤ R n := norm_gamma_path_error_le hw hn
    have hpath : normalizedGamma w = normalizedGamma (n : ℂ) * Complex.exp E := by
      simpa only [Complex.ofReal_natCast] using normalizedGamma_path hw hn
    have he : ‖Complex.exp E‖ ≤ Real.exp (R n) :=
      (Complex.norm_exp_le_exp_norm E).trans (Real.exp_le_exp.mpr hE)
    have he1 : ‖Complex.exp E - 1‖ ≤ Real.exp (R n) - 1 := by
      have h := Complex.norm_exp_sub_sum_le_exp_norm_sub_sum E 1
      simp only [Finset.sum_range_one, pow_zero, Nat.factorial_zero, Nat.cast_one,
        div_one] at h
      exact h.trans (sub_le_sub_right (Real.exp_le_exp.mpr hE) 1)
    calc
      ‖normalizedGamma w - 1‖ =
          ‖(normalizedGamma n - 1) * Complex.exp E + (Complex.exp E - 1)‖ := by
        rw [hpath]
        congr 1
        ring
      _ ≤ ‖normalizedGamma n - 1‖ * ‖Complex.exp E‖ + ‖Complex.exp E - 1‖ := by
        simpa only [norm_mul] using norm_add_le ((normalizedGamma n - 1) * Complex.exp E)
          (Complex.exp E - 1)
      _ ≤ ‖normalizedGamma n - 1‖ * Real.exp (R n) + (Real.exp (R n) - 1) := by
        exact add_le_add (mul_le_mul_of_nonneg_left he (norm_nonneg _)) he1
      _ = _ := by ring
  have hlim : Tendsto (fun n : ℕ =>
      (‖normalizedGamma n - 1‖ + 1) * Real.exp (R n) - 1) atTop
      (𝓝 (Real.exp (2 / w.re) - 1)) := by
    convert! ((hG.add_const 1).mul ((Real.continuous_exp.tendsto _).comp hR)).sub_const 1
      using 1 <;> simp [Function.comp_def]
  exact ge_of_tendsto hlim hbound

lemma norm_normalizedGamma_sub_one_le {w : ℂ} (hw : 2 ≤ w.re) :
    ‖normalizedGamma w - 1‖ ≤ 4 / w.re := by
  have hwpos : 0 < w.re := by linarith
  have hsmall : |(2 : ℝ) / w.re| ≤ 1 := by
    rw [abs_of_pos (by positivity), div_le_one hwpos]
    exact hw
  calc
    ‖normalizedGamma w - 1‖ ≤ Real.exp (2 / w.re) - 1 :=
      norm_normalizedGamma_sub_one_le_exp (by linarith)
    _ ≤ |Real.exp (2 / w.re) - 1| := le_abs_self _
    _ ≤ 2 * |(2 : ℝ) / w.re| := Real.abs_exp_sub_one_le hsmall
    _ = 4 / w.re := by rw [abs_of_pos (by positivity)]; ring

lemma tendsto_normalizedGamma_of_re_tendsto_atTop {α : Type*} {l : Filter α} {w : α → ℂ}
    (hw : Tendsto (fun i => (w i).re) l atTop) :
    Tendsto (fun i => normalizedGamma (w i)) l (𝓝 1) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun i => 4 / (w i).re) l (𝓝 0) :=
    hw.const_div_atTop 4
  apply squeeze_zero' (Eventually.of_forall fun i => norm_nonneg _) _ hlim
  filter_upwards [hw.eventually (eventually_ge_atTop (2 : ℝ))] with i hi
  exact norm_normalizedGamma_sub_one_le hi

end ZudilinZeta.GammaEstimates
end

theorem solution (w : ℂ) (hw : 1 ≤ w.re) :
    ‖Complex.Gamma (w + 1) *
      Complex.exp (-((w + 1 / 2) * Complex.log w - w)) /
      (Real.sqrt (2 * Real.pi) : ℂ) - 1‖ ≤ Real.exp (2 / w.re) - 1 := by
  exact ZudilinZeta.GammaEstimates.norm_normalizedGamma_sub_one_le_exp hw
