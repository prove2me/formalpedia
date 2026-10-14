-- Prove2me | solution 1 for TaoFivePrimes.vonMangoldt_explicit_formula
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-13T19:10:35.559695+00:00
-- url     : https://prove2.me/submissions/55f92cb5-3586-48e0-b89c-62e276376e21

import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Theorems.Thm_Zeta23_Stirling_hasSum_trigamma
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Integral.Prod
import Theorems.Thm_Zeta23_Stirling_differentiableAt_digamma
import Theorems.Thm_Zeta23_digamma_conj
import Definitions.Def_ConnesRZ_weil_defs
import Theorems.Thm_ConnesRZ_explicit_formula_C2
import Mathlib.Analysis.Calculus.MeanValue

/-!
Tao Proposition 7.1 for arbitrary complex smooth compact cutoffs on [2,infinity).
Uses actual critical-strip zeros with analytic multiplicity and proves HasSum.
The original equation's unbound x is corrected to the integration variable u.
Gamma/Fourier conversion is reused from the accepted physical formula proof
c855fb32-3737-493b-9146-933aaa59eb09, with its logarithmic test generalized here.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
open MeasureTheory Set Filter
open scoped Topology

namespace TaoFivePrimes.PhysicalGamma

private theorem real_laplace_moment_integrable (a : ℝ) (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => t * Real.exp (-(a * t))) (Ioi 0) := by
  have hi : IntegrableOn (fun t : ℝ => t * Real.exp (-t)) (Ioi 0) := by
    simpa only [show (2 - 1 : ℝ) = 1 by norm_num, Real.rpow_one, mul_comm] using
      (Real.GammaIntegral_convergent (s := 2) (by norm_num))
  have hc := (integrableOn_Ioi_comp_mul_left_iff (fun t : ℝ => t * Real.exp (-t)) 0 ha).mpr
    (by simpa only [mul_zero] using hi)
  have hd := hc.const_mul a⁻¹
  apply hd.congr
  filter_upwards [] with t
  field_simp [ha.ne']

private theorem laplace_moment_integrable (z : ℂ) (hz : 0 < z.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) * Complex.exp (-z * t)) (Ioi 0) := by
  have hn : IntegrableOn (fun t : ℝ => ‖(t : ℂ) * Complex.exp (-z * t)‖) (Ioi 0) := by
    apply (real_laplace_moment_integrable z.re hz).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
    simp [Complex.norm_exp]
  exact (integrable_norm_iff (by
    apply Continuous.aestronglyMeasurable
    fun_prop)).mp hn

private theorem laplace_moment (z : ℂ) (hz : 0 < z.re) :
    (∫ t : ℝ in Ioi 0, (t : ℂ) * Complex.exp (-z * t)) = 1 / z ^ 2 := by
  have hzn : z ≠ 0 := by intro h; simp [h] at hz
  let F : ℝ → ℂ := fun t => -(t / z + 1 / z ^ 2) * Complex.exp (-z * t)
  have hd : ∀ t : ℝ, HasDerivAt F ((t : ℂ) * Complex.exp (-z * t)) t := by
    intro t
    have h0 := ((hasDerivAt_id t).ofReal_comp.div_const z).add_const (1 / z ^ 2)
    have h1 := ((hasDerivAt_id t).ofReal_comp.const_mul (-z)).cexp
    apply (h0.neg.mul h1).congr_deriv
    dsimp only [id_eq, Pi.neg_apply]
    norm_num only [Complex.ofReal_one]
    field_simp [hzn]
    ring
  have hrate : Tendsto (fun t : ℝ => z.re * t) atTop atTop :=
    tendsto_id.const_mul_atTop hz
  have heReal : Tendsto (fun t : ℝ => Real.exp (-(z.re * t))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hrate)
  have htReal : Tendsto (fun t : ℝ => t * Real.exp (-(z.re * t))) atTop (𝓝 0) := by
    have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hrate
    have hh := h.const_mul z.re⁻¹
    simpa only [Function.comp_apply, pow_one, ← mul_assoc, inv_mul_cancel₀ hz.ne',
      one_mul, mul_zero] using hh
  have he : Tendsto (fun t : ℝ => Complex.exp (-z * t)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa [Complex.norm_exp] using heReal
  have ht : Tendsto (fun t : ℝ => (t : ℂ) * Complex.exp (-z * t)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply htReal.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    simp [norm_mul, Complex.norm_exp, abs_of_pos ht]
  have hF : Tendsto F atTop (𝓝 0) := by
    have h := (ht.const_mul (-(1 / z))).sub (he.const_mul (1 / z ^ 2))
    simp only [mul_zero, sub_zero] at h
    convert h using 1
    funext t
    dsimp [F]
    ring
  have hi := integral_Ioi_of_hasDerivAt_of_tendsto
    (f := F) (f' := fun t => (t : ℂ) * Complex.exp (-z * t))
    (by apply Continuous.continuousWithinAt; dsimp [F]; fun_prop)
    (fun t _ => hd t) (laplace_moment_integrable z hz) hF
  simpa [F] using hi

private theorem real_laplace_moment (a : ℝ) (ha : 0 < a) :
    (∫ t : ℝ in Ioi 0, t * Real.exp (-(a * t))) = 1 / a ^ 2 := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (r := a) (by norm_num) ha
  norm_num only [show (2 - 1 : ℝ) = 1 by norm_num, Real.rpow_one,
    Real.rpow_natCast] at h
  norm_num at h
  simpa [div_pow] using h

private theorem laplace_moment_norm (z : ℂ) (hz : 0 < z.re) :
    (∫ t : ℝ in Ioi 0, ‖(t : ℂ) * Complex.exp (-z * t)‖) = 1 / z.re ^ 2 := by
  rw [← real_laplace_moment z.re hz]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  change 0 < t at ht
  simp [norm_mul, Complex.norm_exp, abs_of_pos ht]

private theorem laplace_kernel_sum (z : ℂ) (t : ℝ) (ht : 0 < t) :
    HasSum (fun n : ℕ => (t : ℂ) * Complex.exp (-(z + n) * t))
      ((t : ℂ) * Complex.exp (-z * t) / (1 - Complex.exp (-(t : ℂ)))) := by
  have hq : ‖Complex.exp (-(t : ℂ))‖ < 1 := by
    rw [Complex.norm_exp]
    simp only [Complex.neg_re, Complex.ofReal_re]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have h := (hasSum_geometric_of_norm_lt_one hq).mul_left
    ((t : ℂ) * Complex.exp (-z * t))
  have hf : (fun n : ℕ => (t : ℂ) * Complex.exp (-z * t) *
      Complex.exp (-(t : ℂ)) ^ n) =
      fun n : ℕ => (t : ℂ) * Complex.exp (-(z + n) * t) := by
    funext n
    rw [← Complex.exp_nat_mul, mul_assoc, ← Complex.exp_add]
    congr 1
    congr 1
    ring
  rw [hf] at h
  simpa only [div_eq_mul_inv] using h

/-- Absolutely convergent Laplace representation, for use in the gamma-side conversion. -/
theorem trigamma_laplace (z : ℂ) (hz : 0 < z.re) (hint : z ∈ Complex.integerComplement) :
    deriv Complex.digamma z =
      ∫ t : ℝ in Ioi 0, (t : ℂ) * Complex.exp (-z * t) /
        (1 - Complex.exp (-(t : ℂ))) := by
  let F : ℕ → ℝ → ℂ := fun n t => (t : ℂ) * Complex.exp (-(z + n) * t)
  have hzN : ∀ n : ℕ, 0 < (z + n).re := by
    intro n
    simp only [Complex.add_re, Complex.natCast_re]
    exact add_pos_of_pos_of_nonneg hz (Nat.cast_nonneg n)
  have hFi : ∀ n : ℕ, IntegrableOn (F n) (Ioi 0) := fun n =>
    laplace_moment_integrable (z + n) (hzN n)
  have hNs : Summable (fun n : ℕ => 1 / (z.re + n) ^ 2) := by
    have h := (Real.summable_one_div_nat_add_rpow z.re 2).mpr (by norm_num)
    convert h using 1
    funext n
    rw [abs_of_pos (by positivity : 0 < (n : ℝ) + z.re), Real.rpow_two]
    congr 1
    ring
  have hNorms : Summable (fun n : ℕ => ∫ t : ℝ in Ioi 0, ‖F n t‖) := by
    apply hNs.congr
    intro n
    simpa only [F, Complex.add_re, Complex.natCast_re] using
      (laplace_moment_norm (z + n) (hzN n)).symm
  have hs := hasSum_integral_of_summable_integral_norm hFi hNorms
  have hcoeff : (fun n : ℕ => ∫ t : ℝ in Ioi 0, F n t) =
      fun n : ℕ => 1 / (z + n) ^ 2 := by
    funext n
    exact laplace_moment (z + n) (hzN n)
  rw [hcoeff] at hs
  have hkernel : (∫ t : ℝ in Ioi 0, ∑' n, F n t) =
      ∫ t : ℝ in Ioi 0, (t : ℂ) * Complex.exp (-z * t) /
        (1 - Complex.exp (-(t : ℂ))) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    exact (laplace_kernel_sum z t ht).tsum_eq
  rw [hkernel] at hs
  exact (Zeta23.Stirling.hasSum_trigamma hint).unique hs

private theorem real_kernel_integrable (a : ℝ) (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => t * Real.exp (-(a * t)) / (1 - Real.exp (-t))) (Ioi 0) := by
  have he : IntegrableOn (fun t : ℝ => Real.exp (-(a * t))) (Ioi 0) := by
    simpa only [neg_mul] using integrableOn_exp_mul_Ioi (a := -a) (by linarith) 0
  have hm := he.add (real_laplace_moment_integrable a ha)
  have hmeas : Measurable (fun t : ℝ => t * Real.exp (-(a * t)) / (1 - Real.exp (-t))) :=
    (show Measurable (fun t : ℝ => t * Real.exp (-(a * t))) by fun_prop).div
      (show Measurable (fun t : ℝ => 1 - Real.exp (-t)) by fun_prop)
  apply hm.mono' hmeas.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  change 0 < t at ht
  have hd : 0 < 1 - Real.exp (-t) := by
    have h := Real.exp_lt_one_iff.mpr (show -t < 0 by linarith)
    linarith
  have hx := mul_le_mul_of_nonneg_left (Real.add_one_le_exp t) (Real.exp_pos (-t)).le
  rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at hx
  have hfrac : t / (1 - Real.exp (-t)) ≤ 1 + t :=
    (div_le_iff₀ hd).mpr (by nlinarith)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc
    _ = (t / (1 - Real.exp (-t))) * Real.exp (-(a * t)) := by ring
    _ ≤ (1 + t) * Real.exp (-(a * t)) :=
      mul_le_mul_of_nonneg_right hfrac (Real.exp_pos _).le
    _ = _ := by dsimp only [Pi.add_apply]; ring

private theorem complex_kernel_integrable (z : ℂ) (hz : 0 < z.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) * Complex.exp (-z * t) /
      (1 - Complex.exp (-(t : ℂ)))) (Ioi 0) := by
  have hn : IntegrableOn (fun t : ℝ => ‖(t : ℂ) * Complex.exp (-z * t) /
      (1 - Complex.exp (-(t : ℂ)))‖) (Ioi 0) := by
    apply (real_kernel_integrable z.re hz).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change 0 < t at ht
    have hd : 0 < 1 - Real.exp (-t) := by
      have h := Real.exp_lt_one_iff.mpr (show -t < 0 by linarith)
      linarith
    have hden : 1 - Complex.exp (-(t : ℂ)) = ((1 - Real.exp (-t) : ℝ) : ℂ) := by
      push_cast <;> rfl
    rw [norm_div, norm_mul, hden, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos ht, abs_of_pos hd]
    simp [Complex.norm_exp]
  have hmeas : Measurable (fun t : ℝ => (t : ℂ) * Complex.exp (-z * t) /
      (1 - Complex.exp (-(t : ℂ)))) :=
    (show Measurable (fun t : ℝ => (t : ℂ) * Complex.exp (-z * t)) by fun_prop).div
      (show Measurable (fun t : ℝ => (1 : ℂ) - Complex.exp (-(t : ℂ))) by fun_prop)
  exact (integrable_norm_iff hmeas.aestronglyMeasurable).mp hn

end TaoFivePrimes.PhysicalGamma

set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory
open scoped FourierTransform

namespace TaoFivePrimes.PhysicalFourier

private noncomputable def FT (h : ℝ → ℂ) (r : ℝ) : ℂ :=
  ∫ v : ℝ, h v * Complex.exp (Complex.I * r * v)

private theorem FT_eq_fourier (h : ℝ → ℂ) (r : ℝ) :
    FT h r = 𝓕 h (-r / (2 * Real.pi)) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  unfold FT
  apply integral_congr_ae
  filter_upwards [] with v
  simp only [smul_eq_mul]
  have he : Complex.I * (r : ℂ) * v =
      ((-2 * Real.pi * v * (-r / (2 * Real.pi)) : ℝ) : ℂ) * Complex.I := by
    push_cast
    field_simp [Real.pi_ne_zero] <;> ring
  rw [he, mul_comm]

private theorem FT_schwartz_integrable (h : SchwartzMap ℝ ℂ) : Integrable (FT h) := by
  have hf : Integrable (𝓕 (fun x : ℝ => h x)) := by
    simpa only [SchwartzMap.fourier_coe] using (𝓕 h).integrable
  have hrate : -(2 * Real.pi)⁻¹ ≠ (0 : ℝ) :=
    neg_ne_zero.mpr (inv_ne_zero (by positivity))
  have hcomp := (integrable_comp_mul_left_iff (𝓕 (fun x : ℝ => h x)) hrate).mpr hf
  apply hcomp.congr
  filter_upwards [] with r
  rw [FT_eq_fourier]
  congr 1
  try dsimp
  ring

private theorem inverse_pair (h : SchwartzMap ℝ ℂ) (w : ℝ) :
    (∫ r : ℝ, FT h r * Complex.exp (-Complex.I * r * w)) = (2 * Real.pi : ℂ) * h w := by
  have hf : Integrable (𝓕 (fun x : ℝ => h x)) := by
    simpa only [SchwartzMap.fourier_coe] using (𝓕 h).integrable
  have hinv := h.continuous.fourierInv_fourier_eq h.integrable hf
  let G : ℝ → ℂ := fun r => FT h r * Complex.exp (-Complex.I * r * w)
  have hchange := MeasureTheory.Measure.integral_comp_mul_left G (-2 * Real.pi)
  have heq : (fun r : ℝ => G ((-2 * Real.pi) * r)) =
      fun r : ℝ => Complex.exp ((2 * Real.pi * r * w : ℝ) * Complex.I) *
        𝓕 (fun x : ℝ => h x) r := by
    funext r
    dsimp [G]
    rw [FT_eq_fourier]
    have hr : -((-2 * Real.pi) * r) / (2 * Real.pi) = r := by
      field_simp [Real.pi_ne_zero]
    rw [hr]
    have hp : -Complex.I * ((-2 * Real.pi) * r : ℝ) * w =
        (2 * Real.pi * r * w : ℝ) * Complex.I := by push_cast; ring
    rw [hp, mul_comm]
  rw [heq] at hchange
  have hi : (∫ r : ℝ, Complex.exp ((2 * Real.pi * r * w : ℝ) * Complex.I) *
      𝓕 (fun x : ℝ => h x) r) = h w := by
    have hiw := congrFun hinv w
    rw [Real.fourierInv_eq'] at hiw
    simp only [smul_eq_mul, RCLike.inner_apply, conj_trivial, RCLike.re_to_real] at hiw
    calc
      _ = (∫ r : ℝ, Complex.exp ((2 * Real.pi * (w * r) : ℝ) * Complex.I) *
          𝓕 (fun x : ℝ => h x) r) := by
        apply integral_congr_ae
        filter_upwards [] with r
        have he : ((2 * Real.pi * r * w : ℝ) : ℂ) * Complex.I =
            ((2 * Real.pi * (w * r) : ℝ) : ℂ) * Complex.I := by push_cast; ring
        rw [he]
      _ = _ := hiw
  rw [hi] at hchange
  simp only [show (-2 * Real.pi : ℝ) = -(2 * Real.pi) by ring, abs_inv, abs_neg,
    abs_of_pos (by positivity : 0 < (2 * Real.pi : ℝ)),
    Complex.real_smul, Complex.ofReal_inv] at hchange
  push_cast at hchange
  change h w = (2 * Real.pi : ℂ)⁻¹ * (∫ r : ℝ, G r) at hchange
  calc
    _ = (2 * Real.pi : ℂ) * ((2 * Real.pi : ℂ)⁻¹ * (∫ r : ℝ, G r)) := by
      rw [← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast (show (2 * Real.pi : ℝ) ≠ 0 by positivity)), one_mul]
    _ = _ := by rw [← hchange]

end TaoFivePrimes.PhysicalFourier

namespace TaoFivePrimes.PhysicalPairing
open TaoFivePrimes.PhysicalFourier TaoFivePrimes.PhysicalGamma

private noncomputable def K (a t : ℝ) : ℂ :=
  (t : ℂ) * Complex.exp (-(a : ℂ) * t) / (1 - Complex.exp (-(t : ℂ)))

private theorem cmul_integral (c : ℂ) (f : ℝ → ℂ) (mu : Measure ℝ) :
    (∫ x : ℝ, c * f x ∂mu) = c * ∫ x : ℝ, f x ∂mu := by
  exact integral_const_mul c f

private theorem FT_continuous (h : SchwartzMap ℝ ℂ) : Continuous (FT h) := by
  have he : FT h = fun r : ℝ => (𝓕 h) (-r / (2 * Real.pi)) := by
    funext r
    rw [FT_eq_fourier]
    rfl
  rw [he]
  exact (𝓕 h).continuous.comp (by fun_prop)

private theorem laplace_pair (h : SchwartzMap ℝ ℂ) (a : ℝ) (ha : 0 < a) :
    (∫ r : ℝ, FT h r * (∫ t : ℝ in Set.Ioi 0,
      K a t * Complex.exp (-Complex.I * r * t / 2))) =
      (2 * Real.pi : ℂ) * (∫ t : ℝ in Set.Ioi 0, K a t * h (t / 2)) := by
  let nu := volume.restrict (Set.Ioi (0 : ℝ))
  have hK : Integrable (K a) nu := complex_kernel_integrable (a : ℂ) ha
  have hKm : Measurable (K a) := by
    unfold K
    exact (show Measurable (fun t : ℝ => (t : ℂ) * Complex.exp (-(a : ℂ) * t)) by
      fun_prop).div (show Measurable (fun t : ℝ => (1 : ℂ) - Complex.exp (-(t : ℂ))) by
      fun_prop)
  have hmajor := (FT_schwartz_integrable h).norm.mul_prod hK.norm
  have hJoint : Integrable (fun p : ℝ × ℝ => FT h p.1 *
      (K a p.2 * Complex.exp (-Complex.I * p.1 * p.2 / 2))) (volume.prod nu) := by
    have hm : Measurable (fun p : ℝ × ℝ => FT h p.1 *
        (K a p.2 * Complex.exp (-Complex.I * p.1 * p.2 / 2))) :=
      (((FT_continuous h).measurable.comp measurable_fst).mul
        ((hKm.comp measurable_snd).mul (by fun_prop)))
    apply hmajor.mono' hm.aestronglyMeasurable
    filter_upwards [] with p
    have he : ‖Complex.exp (-Complex.I * p.1 * p.2 / 2)‖ = 1 := by
      simp [Complex.norm_exp]
    simp only [norm_mul, he, mul_one, le_refl]
  have hswap := integral_integral_swap
    (f := fun r t : ℝ => FT h r * (K a t * Complex.exp (-Complex.I * r * t / 2))) hJoint
  have hinner : ∀ t : ℝ, (∫ r : ℝ, FT h r *
      (K a t * Complex.exp (-Complex.I * r * t / 2))) = K a t * ((2 * Real.pi : ℂ) * h (t / 2)) := by
    intro t
    have he : (fun r : ℝ => FT h r * (K a t * Complex.exp (-Complex.I * r * t / 2))) =
        fun r : ℝ => K a t * (FT h r * Complex.exp (-Complex.I * r * ((t / 2 : ℝ) : ℂ))) := by
      funext r
      push_cast
      ring
    rw [he, cmul_integral, inverse_pair]
  calc
    _ = ∫ r : ℝ, ∫ t : ℝ, FT h r * (K a t * Complex.exp (-Complex.I * r * t / 2)) ∂nu := by
      apply integral_congr_ae
      filter_upwards [] with r
      exact (cmul_integral (FT h r) _ nu).symm
    _ = ∫ t : ℝ, (∫ r : ℝ, FT h r * (K a t * Complex.exp (-Complex.I * r * t / 2))) ∂nu := hswap
    _ = ∫ t : ℝ, K a t * ((2 * Real.pi : ℂ) * h (t / 2)) ∂nu := by
      simp_rw [hinner]
    _ = _ := by
      rw [← cmul_integral]
      apply integral_congr_ae
      filter_upwards [] with t
      ring

private theorem gamma_line_noninteger (r : ℝ) :
    (1 / 4 + Complex.I * r / 2 : ℂ) ∈ Complex.integerComplement := by
  rw [Complex.mem_integerComplement_iff]
  rintro ⟨n, hn⟩
  have hre := congrArg Complex.re hn
  simp at hre
  have h0 : (0 : ℝ) < (n : ℝ) := by linarith
  have h1 : (n : ℝ) < 1 := by linarith
  have hn0 : (0 : ℤ) < n := by exact_mod_cast h0
  have hn1 : n < (1 : ℤ) := by exact_mod_cast h1
  omega

private theorem kernel_trigamma (r : ℝ) :
    (∫ t : ℝ in Set.Ioi 0, K (1 / 4) t * Complex.exp (-Complex.I * r * t / 2)) =
      deriv Complex.digamma (1 / 4 + Complex.I * r / 2) := by
  rw [trigamma_laplace _ (by norm_num) (gamma_line_noninteger r)]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  unfold K
  push_cast
  have he : -((1 / 4 : ℂ) + Complex.I * r / 2) * t =
      -(1 / 4 : ℂ) * t + (-Complex.I * r * t / 2) := by ring
  rw [he, Complex.exp_add]
  ring

private theorem trigamma_pair (h : SchwartzMap ℝ ℂ) :
    (∫ r : ℝ, FT h r * deriv Complex.digamma (1 / 4 + Complex.I * r / 2)) =
      (2 * Real.pi : ℂ) * (∫ t : ℝ in Set.Ioi 0, K (1 / 4) t * h (t / 2)) := by
  simp_rw [← kernel_trigamma]
  exact laplace_pair h (1 / 4) (by norm_num)

private theorem kernel_rescale (h : SchwartzMap ℝ ℂ) :
    (∫ t : ℝ in Set.Ioi 0, K (1 / 4) t * h (t / 2)) =
      (4 : ℂ) * (∫ v : ℝ in Set.Ioi 0, (v : ℂ) * h v * Complex.exp (-(v : ℂ) / 2) /
        (1 - Complex.exp (-2 * (v : ℂ)))) := by
  let f : ℝ → ℂ := fun t => K (1 / 4) t * h (t / 2)
  have hc := integral_comp_mul_left_Ioi f 0 (b := 2) (by norm_num)
  have hfn : (fun v : ℝ => f (2 * v)) = fun v : ℝ =>
      (2 : ℂ) * ((v : ℂ) * h v * Complex.exp (-(v : ℂ) / 2) /
        (1 - Complex.exp (-2 * (v : ℂ)))) := by
    funext v
    dsimp [f, K]
    rw [show (2 * v / 2 : ℝ) = v by ring]
    push_cast
    have h0 : -(1 / 4 : ℂ) * (2 * v) = -(v : ℂ) / 2 := by ring
    have h1 : -(2 * (v : ℂ)) = -2 * (v : ℂ) := by ring
    rw [h0, h1]
    ring
  rw [hfn, cmul_integral] at hc
  norm_num only [mul_zero, Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_ofNat] at hc
  push_cast at hc
  dsimp [f] at hc
  linear_combination -(2 : ℂ) * hc

private theorem trigamma_pair_rescaled (h : SchwartzMap ℝ ℂ) :
    (∫ r : ℝ, FT h r * deriv Complex.digamma (1 / 4 + Complex.I * r / 2)) =
      (8 * Real.pi : ℂ) * (∫ v : ℝ in Set.Ioi 0, (v : ℂ) * h v * Complex.exp (-(v : ℂ) / 2) /
        (1 - Complex.exp (-2 * (v : ℂ)))) := by
  rw [trigamma_pair, kernel_rescale]
  ring

end TaoFivePrimes.PhysicalPairing

namespace TaoFivePrimes.PhysicalConversion
open TaoFivePrimes.PhysicalFourier TaoFivePrimes.PhysicalPairing

private noncomputable def psiLine (r : ℝ) : ℂ :=
  Complex.digamma (1 / 4 + Complex.I * r / 2)

private noncomputable def triLine (r : ℝ) : ℂ :=
  deriv Complex.digamma (1 / 4 + Complex.I * r / 2)

private theorem psiLine_deriv (r : ℝ) :
    HasDerivAt psiLine (triLine r * (Complex.I / 2)) r := by
  change HasDerivAt (fun x : ℝ => Complex.digamma (1 / 4 + Complex.I * x / 2))
    (deriv Complex.digamma (1 / 4 + Complex.I * r / 2) * (Complex.I / 2)) r
  have hd := (Zeta23.Stirling.differentiableAt_digamma
    (gamma_line_noninteger r)).hasDerivAt
  have hl := (((hasDerivAt_id r).ofReal_comp.const_mul Complex.I).div_const 2).const_add
    (1 / 4 : ℂ)
  simpa only [Function.comp_def, id_eq, smul_eq_mul, Complex.ofReal_one, mul_one,
    mul_comm] using hd.scomp r hl

private noncomputable def triBound : ℝ := ∫ t : ℝ in Ioi 0, ‖K (1 / 4) t‖

private theorem triLine_bound (r : ℝ) : ‖triLine r‖ ≤ triBound := by
  rw [triLine, ← kernel_trigamma]
  calc
    _ ≤ ∫ t : ℝ in Ioi 0, ‖K (1 / 4) t * Complex.exp (-Complex.I * r * t / 2)‖ :=
      norm_integral_le_integral_norm _
    _ = triBound := by
      unfold triBound
      apply integral_congr_ae
      filter_upwards [] with t
      simp [norm_mul, Complex.norm_exp]

private noncomputable def bracket (r : ℝ) : ℂ :=
  (psiLine r + psiLine (-r)) / 2 - (Real.log Real.pi : ℂ)

private noncomputable def bracketDeriv (r : ℝ) : ℂ :=
  (Complex.I / 4) * (triLine r - triLine (-r))

private theorem bracket_deriv (r : ℝ) : HasDerivAt bracket (bracketDeriv r) r := by
  have hm := (psiLine_deriv (-r)).scomp r (hasDerivAt_neg (r : ℝ))
  change HasDerivAt (fun x : ℝ => (psiLine x + psiLine (-x)) / 2 -
    (Real.log Real.pi : ℂ)) (bracketDeriv r) r
  apply ((((psiLine_deriv r).add hm).div_const 2).sub_const
    (Real.log Real.pi : ℂ)).congr_deriv
  dsimp only [bracketDeriv]
  simp only [neg_smul, one_smul]
  ring

private theorem bracket_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ r, ‖bracket r‖ ≤ C * (1 + ‖r‖) := by
  have hB : 0 ≤ triBound := integral_nonneg (fun _ => norm_nonneg _)
  have hd : ∀ r, ‖bracketDeriv r‖ ≤ triBound := by
    intro r
    calc
      _ = (1 / 4 : ℝ) * ‖triLine r - triLine (-r)‖ := by
        simp [bracketDeriv, norm_mul, norm_div]
      _ ≤ (1 / 4 : ℝ) * (‖triLine r‖ + ‖triLine (-r)‖) := by
        gcongr; exact norm_sub_le _ _
      _ ≤ (1 / 4 : ℝ) * (triBound + triBound) := by
        gcongr <;> exact triLine_bound _
      _ ≤ triBound := by linarith
  have hL (r : ℝ) : ‖bracket r - bracket 0‖ ≤ triBound * ‖r‖ := by
    simpa only [sub_zero] using Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (s := Set.univ) (fun x _ => (bracket_deriv x).hasDerivWithinAt)
      (fun x _ => hd x) convex_univ (mem_univ 0) (mem_univ r)
  refine ⟨‖bracket 0‖ + triBound, by positivity, fun r => ?_⟩
  calc
    _ ≤ ‖bracket r - bracket 0‖ + ‖bracket 0‖ := norm_le_norm_sub_add _ _
    _ ≤ triBound * ‖r‖ + ‖bracket 0‖ := by gcongr; exact hL r
    _ ≤ _ := by nlinarith [norm_nonneg r, norm_nonneg (bracket 0)]

private noncomputable def FTSchwartz (h : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := ℝ)
      (Units.mk0 (-(2 * Real.pi)⁻¹) (neg_ne_zero.mpr (inv_ne_zero (by positivity))))) (𝓕 h)

private theorem FTSchwartz_apply (h : SchwartzMap ℝ ℂ) (r : ℝ) :
    FTSchwartz h r = FT h r := by
  rw [FT_eq_fourier]
  change (𝓕 h) (-(2 * Real.pi)⁻¹ • r) = _
  congr 1
  simp [SchwartzMap.fourier_coe, div_eq_mul_inv, mul_comm]

private theorem FT_bracket_integrable (h : SchwartzMap ℝ ℂ) :
    Integrable (fun r => FT h r * bracket r) := by
  obtain ⟨C, hC, hb⟩ := bracket_bound
  have hw := ((FTSchwartz h).integrable.norm.add
    ((FTSchwartz h).integrable_pow_mul volume 1)).const_mul C
  apply hw.mono' ((FT_continuous h).mul
    (show Continuous bracket from continuous_iff_continuousAt.mpr
      (fun r => (bracket_deriv r).continuousAt))).aestronglyMeasurable
  filter_upwards [] with r
  simp only [Pi.add_apply, pow_one, FTSchwartz_apply] at *
  change ‖FT h r * bracket r‖ ≤ _
  rw [norm_mul]
  calc
    _ ≤ ‖FT h r‖ * (C * (1 + ‖r‖)) := mul_le_mul_of_nonneg_left (hb r) (norm_nonneg _)
    _ = _ := by ring

private theorem FT_bracketDeriv_integrable (h : SchwartzMap ℝ ℂ) :
    Integrable (fun r => FT h r * bracketDeriv r) := by
  have hB : 0 ≤ triBound := integral_nonneg (fun _ => norm_nonneg _)
  have hd : ∀ r, ‖bracketDeriv r‖ ≤ triBound := by
    intro r
    calc
      _ = (1 / 4 : ℝ) * ‖triLine r - triLine (-r)‖ := by
        simp [bracketDeriv, norm_mul, norm_div]
      _ ≤ (1 / 4 : ℝ) * (‖triLine r‖ + ‖triLine (-r)‖) := by
        gcongr; exact norm_sub_le _ _
      _ ≤ (1 / 4 : ℝ) * (triBound + triBound) := by
        gcongr <;> exact triLine_bound _
      _ ≤ triBound := by linarith
  have hcont : Continuous triLine := by
    have he : triLine = fun r : ℝ => deriv Complex.digamma (1 / 4 + Complex.I * r / 2) := rfl
    rw [he]
    have hdiff : DifferentiableOn ℂ Complex.digamma Complex.integerComplement :=
      fun z hz => (Zeta23.Stirling.differentiableAt_digamma hz).differentiableWithinAt
    exact (hdiff.analyticOnNhd Complex.isOpen_compl_range_intCast).deriv.continuousOn.comp_continuous
      (by fun_prop) (fun r => gamma_line_noninteger r)
  have hm : Continuous bracketDeriv := by
    unfold bracketDeriv
    exact continuous_const.mul (hcont.sub (hcont.comp continuous_neg))
  apply ((FT_schwartz_integrable h).norm.const_mul triBound).mono'
    ((FT_continuous h).mul hm).aestronglyMeasurable
  filter_upwards [] with r
  change ‖FT h r * bracketDeriv r‖ ≤ _
  rw [norm_mul]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hd r) (norm_nonneg (FT h r))

private theorem FT_deriv (h g : SchwartzMap ℝ ℂ)
    (hrel : ∀ v : ℝ, Complex.I * v * h v = g v) (r : ℝ) :
    HasDerivAt (FT h) (FT g r) r := by
  have hw : Integrable (fun v : ℝ => v • h v) := by
    apply (integrable_norm_iff (by fun_prop)).mp
    simpa only [norm_smul, pow_one] using h.integrable_pow_mul volume 1
  have hd := Real.hasDerivAt_fourier h.integrable hw (-r / (2 * Real.pi))
  have hc := hd.scomp r ((hasDerivAt_id r).neg.div_const (2 * Real.pi))
  have he : (fun r : ℝ => 𝓕 (fun v : ℝ => h v) (-r / (2 * Real.pi))) = FT h := by
    funext r; exact (FT_eq_fourier h r).symm
  change HasDerivAt (fun r : ℝ => 𝓕 (fun v : ℝ => h v) (-r / (2 * Real.pi)))
    ((-1 / (2 * Real.pi) : ℝ) •
      𝓕 (fun v : ℝ => (-2 * Real.pi * Complex.I * v) • h v) (-r / (2 * Real.pi))) r at hc
  rw [he] at hc
  apply hc.congr_deriv
  rw [Complex.real_smul, FT_eq_fourier, Real.fourier_real_eq_integral_exp_smul,
    Real.fourier_real_eq_integral_exp_smul, ← cmul_integral]
  apply integral_congr_ae
  filter_upwards [] with v
  rw [← hrel v]
  simp only [smul_eq_mul]
  push_cast
  field_simp [Real.pi_ne_zero] <;> ring

private noncomputable def reflectSchwartz (h : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (ContinuousLinearEquiv.neg ℝ) h

private theorem reflectSchwartz_apply (h : SchwartzMap ℝ ℂ) (v : ℝ) :
    reflectSchwartz h v = h (-v) := rfl

private theorem FT_reflect (h : SchwartzMap ℝ ℂ) (r : ℝ) :
    FT (reflectSchwartz h) r = FT h (-r) := by
  unfold FT
  rw [← integral_neg_eq_self
    (fun v : ℝ => h v * Complex.exp (Complex.I * ((-r : ℝ) : ℂ) * v)) volume]
  apply integral_congr_ae
  filter_upwards [] with v
  rw [reflectSchwartz_apply]
  congr 1
  congr 1
  push_cast
  ring

private theorem trigamma_negative_pair_zero (h : SchwartzMap ℝ ℂ)
    (hsupp : Function.support (fun v : ℝ => h v) ⊆ Ioi 0) :
    (∫ r : ℝ, FT h r * triLine (-r)) = 0 := by
  rw [← integral_neg_eq_self (fun r : ℝ => FT h r * triLine (-r)) volume]
  simp only [neg_neg]
  simp_rw [← FT_reflect]
  simp_rw [triLine]
  rw [trigamma_pair_rescaled]
  have hz : (∫ v : ℝ in Ioi 0, (v : ℂ) * reflectSchwartz h v * Complex.exp (-(v : ℂ) / 2) /
      (1 - Complex.exp (-2 * (v : ℂ)))) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    have hh : h (-v) = 0 := by
      apply Function.notMem_support.mp
      intro hh
      have hp := hsupp hh
      change 0 < -v at hp
      change 0 < v at hv
      linarith
    simp [reflectSchwartz_apply, hh]
  rw [hz, mul_zero]

private theorem FT_tri_integrable (h : SchwartzMap ℝ ℂ) (sign : ℝ) :
    Integrable (fun r => FT h r * triLine (sign * r)) := by
  have hdiff : DifferentiableOn ℂ Complex.digamma Complex.integerComplement :=
    fun z hz => (Zeta23.Stirling.differentiableAt_digamma hz).differentiableWithinAt
  have ht : Continuous triLine :=
    (hdiff.analyticOnNhd Complex.isOpen_compl_range_intCast).deriv.continuousOn.comp_continuous
      (by fun_prop) (fun r => gamma_line_noninteger r)
  apply ((FT_schwartz_integrable h).norm.const_mul triBound).mono'
    ((FT_continuous h).mul (ht.comp (by fun_prop))).aestronglyMeasurable
  filter_upwards [] with r
  change ‖FT h r * triLine (sign * r)‖ ≤ triBound * ‖FT h r‖
  rw [norm_mul, mul_comm triBound]
  exact mul_le_mul_of_nonneg_left (triLine_bound _) (norm_nonneg _)

private theorem bracket_eq (r : ℝ) :
    bracket r = (((Complex.digamma (1 / 4 + Complex.I * r / 2)).re -
      Real.log Real.pi : ℝ) : ℂ) := by
  have hc : psiLine (-r) = star (psiLine r) := by
    unfold psiLine
    change Complex.digamma (1 / 4 + Complex.I * ((-r : ℝ) : ℂ) / 2) =
      (starRingEnd ℂ) (Complex.digamma (1 / 4 + Complex.I * r / 2))
    rw [← Zeta23.digamma_conj]
    congr 1
    simp only [map_add, map_div₀, map_mul, map_one, map_ofNat, Complex.conj_I,
      Complex.conj_ofReal, Complex.ofReal_neg]
    ring
  unfold bracket
  rw [hc]
  have hs : psiLine r + star (psiLine r) = (2 : ℂ) * (psiLine r).re := by
    apply Complex.ext <;> simp [Complex.star_def] <;> ring
  rw [hs]
  dsimp [psiLine]
  push_cast
  ring

theorem archTerm_of_division (g h : SchwartzMap ℝ ℂ)
    (hrel : ∀ v : ℝ, Complex.I * v * h v = g v)
    (hsupp : Function.support (fun v : ℝ => h v) ⊆ Ioi 0) :
    ConnesRZ.archTerm g =
      -(∫ v : ℝ in Ioi 0, g v * Complex.exp (-(v : ℂ) / 2) /
        (1 - Complex.exp (-2 * (v : ℂ)))) := by
  have hparts := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := bracket) (u' := bracketDeriv) (v := FT h) (v' := FT g)
    (fun r _ => bracket_deriv r) (fun r _ => FT_deriv h g hrel r)
    (by change Integrable (fun r => bracket r * FT g r)
        simpa only [mul_comm] using FT_bracket_integrable g)
    (by change Integrable (fun r => bracketDeriv r * FT h r)
        simpa only [mul_comm] using FT_bracketDeriv_integrable h)
    (by change Integrable (fun r => bracket r * FT h r)
        simpa only [mul_comm] using FT_bracket_integrable h)
  have hiP : Integrable (fun r => FT h r * triLine r) := by
    simpa using FT_tri_integrable h 1
  have hiN : Integrable (fun r => FT h r * triLine (-r)) := by
    simpa using FT_tri_integrable h (-1)
  have hd : (∫ r : ℝ, bracketDeriv r * FT h r) =
      (Complex.I / 4) * ((∫ r : ℝ, FT h r * triLine r) -
        (∫ r : ℝ, FT h r * triLine (-r))) := by
    rw [← integral_sub hiP hiN, ← cmul_integral]
    apply integral_congr_ae
    filter_upwards [] with r
    dsimp [bracketDeriv]
    ring
  rw [hd, trigamma_negative_pair_zero h hsupp, sub_zero] at hparts
  unfold triLine at hparts
  rw [trigamma_pair_rescaled] at hparts
  have he : (∫ r : ℝ, bracket r * FT g r) =
      (∫ r : ℝ, FT g r * bracket r) := by
    apply integral_congr_ae; filter_upwards [] with r; ring
  rw [he] at hparts
  have hft : ∀ r : ℝ, ConnesRZ.mellinHat g (1 / 2 + Complex.I * r) = FT g r := by
    intro r
    unfold ConnesRZ.mellinHat FT
    congr 1
    funext v
    congr 1
    congr 1
    ring
  unfold ConnesRZ.archTerm
  change (1 / (2 * Real.pi) : ℂ) * _ = _
  simp_rw [hft, show ∀ r : ℝ,
    (((logDeriv Complex.Gamma (1 / 4 + Complex.I * r / 2)).re -
      Real.log Real.pi : ℝ) : ℂ) = bracket r from fun r => (bracket_eq r).symm]
  rw [hparts]
  have hi : (∫ v : ℝ in Ioi 0, g v * Complex.exp (-(v : ℂ) / 2) /
      (1 - Complex.exp (-2 * (v : ℂ)))) =
      Complex.I * (∫ v : ℝ in Ioi 0, (v : ℂ) * h v * Complex.exp (-(v : ℂ) / 2) /
      (1 - Complex.exp (-2 * (v : ℂ)))) := by
    rw [← cmul_integral]
    apply integral_congr_ae
    filter_upwards [] with v
    rw [← hrel v]
    ring
  rw [hi]
  field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero] <;> ring

end TaoFivePrimes.PhysicalConversion

namespace TaoFivePrimes.Prop71

private noncomputable def logTest (eta : ℝ → ℂ) (v : ℝ) : ℂ :=
  Complex.exp ((v : ℂ) / 2) * eta (Real.exp v)

private theorem logTest_smooth (eta : ℝ → ℂ) (heta : ContDiff ℝ (⊤ : ℕ∞) eta) :
    ContDiff ℝ (⊤ : ℕ∞) (logTest eta) :=
  ((Complex.ofRealCLM.contDiff.div_const (2 : ℂ)).cexp).mul (heta.comp Real.contDiff_exp)

private theorem logTest_support (eta : ℝ → ℂ)
    (hsupp : ∀ u, eta u ≠ 0 → 2 ≤ u) :
    Function.support (logTest eta) ⊆ Ici (Real.log 2) := by
  intro v hv
  have he : eta (Real.exp v) ≠ 0 := by intro h; exact hv (by simp [logTest, h])
  exact (Real.log_le_iff_le_exp (by norm_num : 0 < (2 : ℝ))).mpr (hsupp _ he)

private theorem logTest_tsupport (eta : ℝ → ℂ)
    (hsupp : ∀ u, eta u ≠ 0 → 2 ≤ u) :
    tsupport (logTest eta) ⊆ Ici (Real.log 2) :=
  closure_minimal (logTest_support eta hsupp) isClosed_Ici

private theorem logTest_pos_support (eta : ℝ → ℂ)
    (hsupp : ∀ u, eta u ≠ 0 → 2 ≤ u) :
    tsupport (logTest eta) ⊆ Ioi 0 := by
  intro v hv
  exact (Real.log_pos (by norm_num : 1 < (2 : ℝ))).trans_le (logTest_tsupport eta hsupp hv)

private theorem logTest_compact (eta : ℝ → ℂ) (hc : HasCompactSupport eta)
    (hsupp : ∀ u, eta u ≠ 0 → 2 ≤ u) : HasCompactSupport (logTest eta) := by
  obtain ⟨B, hB⟩ := hc.bddAbove
  apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
  intro v hv
  have he : eta (Real.exp v) ≠ 0 := by intro h; exact hv (by simp [logTest, h])
  have hbe : Real.exp v ≤ B := hB (subset_tsupport eta he)
  have hbp : 0 < B := (Real.exp_pos v).trans_le hbe
  exact ⟨logTest_support eta hsupp hv, (Real.le_log_iff_exp_le hbp).mpr hbe⟩

private theorem integral_supported (f : ℝ → ℂ) (s : Set ℝ) (hs : MeasurableSet s)
    (hf : Function.support f ⊆ s) : (∫ t : ℝ, f t) = ∫ t : ℝ in s, f t := by
  rw [← integral_indicator hs]
  congr 1
  funext t
  by_cases ht : t ∈ s
  · simp [ht]
  · have h0 : f t = 0 := Function.notMem_support.mp (fun h => ht (hf h))
    simp [ht, h0]

private theorem change_exp (f : ℝ → ℂ) :
    (∫ v : ℝ in Ioi 0, (Real.exp v : ℂ) * f (Real.exp v)) = ∫ u : ℝ in Ioi 1, f u := by
  simpa only [Real.exp_zero, Complex.real_smul] using integral_comp_exp_Ioi f 0

private theorem exp_cpow (v : ℝ) (rho : ℂ) :
    (Real.exp v : ℂ) ^ rho = Complex.exp ((v : ℂ) * rho) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos v).ne'),
    ← Complex.ofReal_log (Real.exp_pos v).le, Real.log_exp]

private theorem mellin_dictionary (eta : ℝ → ℂ)
    (hsupp : ∀ u, eta u ≠ 0 → 2 ≤ u) (rho : ℂ) :
    ConnesRZ.mellinHat (logTest eta) rho = ∫ u : ℝ, eta u * (u : ℂ) ^ (rho - 1) := by
  let f : ℝ → ℂ := fun u => eta u * (u : ℂ) ^ (rho - 1)
  have hf : Function.support f ⊆ Ioi 1 := by
    intro u hu
    have he : eta u ≠ 0 := by intro h; exact hu (by simp [f, h])
    exact lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) (hsupp _ he)
  have hg : Function.support (fun v => logTest eta v * Complex.exp ((rho - 1 / 2) * v)) ⊆ Ioi 0 := by
    intro v hv
    have he : logTest eta v ≠ 0 := by intro h; exact hv (by simp [h])
    exact logTest_pos_support eta hsupp (subset_tsupport _ he)
  have hfn : (fun v : ℝ => logTest eta v * Complex.exp ((rho - 1 / 2) * v)) =
      fun v : ℝ => (Real.exp v : ℂ) * f (Real.exp v) := by
    funext v
    have he : Complex.exp ((v : ℂ) / 2) * Complex.exp ((rho - 1 / 2) * v) =
        Complex.exp (v : ℂ) * Complex.exp ((v : ℂ) * (rho - 1)) := by
      rw [← Complex.exp_add, ← Complex.exp_add]
      congr 1
      ring
    calc
      _ = (Complex.exp ((v : ℂ) / 2) * Complex.exp ((rho - 1 / 2) * v)) * eta (Real.exp v) := by
        dsimp [logTest]; ring
      _ = _ := by dsimp [f]; rw [he, exp_cpow, Complex.ofReal_exp]; ring
  unfold ConnesRZ.mellinHat
  rw [integral_supported _ (Ioi 0) measurableSet_Ioi hg, hfn, change_exp,
    ← integral_supported f (Ioi 1) measurableSet_Ioi hf]

private theorem prime_dictionary (eta : ℝ → ℂ)
    (hsupp : ∀ u, eta u ≠ 0 → 2 ≤ u) :
    ConnesRZ.primeSum (logTest eta) =
      ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) * eta n := by
  unfold ConnesRZ.primeSum
  apply tsum_congr
  intro n
  by_cases hn0 : n = 0
  · simp [hn0]
  by_cases hn1 : n = 1
  · simp [hn1]
  have hn2 : 2 ≤ n := by omega
  have hnp : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hnn : 1 ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
  have hneg : logTest eta (-Real.log n) = 0 := by
    apply Function.notMem_support.mp
    intro h
    have hp := logTest_pos_support eta hsupp (subset_tsupport _ h)
    have hl := Real.log_nonneg hnn
    change 0 < -Real.log (n : ℝ) at hp
    linarith
  rw [hneg, add_zero]
  have hexp : Complex.exp ((Real.log n : ℂ) / 2) = (Real.sqrt n : ℂ) := by
    have harg : (Real.log n : ℂ) / 2 = ((Real.log n / 2 : ℝ) : ℂ) := by push_cast; rfl
    rw [harg, ← Complex.ofReal_exp, Real.exp_half, Real.exp_log hnp]
  unfold logTest
  rw [hexp, Real.exp_log hnp]
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hnp).ne'] <;> ring
private theorem divide_smooth (g : ℝ → ℂ) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (h0 : 0 ∉ tsupport g) :
    ContDiff ℝ (⊤ : ℕ∞) (fun v : ℝ => g v / (Complex.I * v)) := by
  rw [contDiff_iff_contDiffAt]
  intro v
  by_cases hv : v = 0
  · subst v
    have he : (fun v : ℝ => g v / (Complex.I * v)) =ᶠ[𝓝 0] (fun _ => (0 : ℂ)) := by
      filter_upwards [(isClosed_tsupport g).isOpen_compl.mem_nhds h0] with x hx
      simp [image_eq_zero_of_notMem_tsupport hx]
    exact (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq he
  · simp only [div_eq_mul_inv]
    exact hg.contDiffAt.mul
      (((contDiff_const (c := Complex.I)).mul Complex.ofRealCLM.contDiff).contDiffAt.inv
        (mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hv)))

private theorem divide_compact (g : ℝ → ℂ) (hg : HasCompactSupport g) :
    HasCompactSupport (fun v : ℝ => g v / (Complex.I * v)) := by
  have he : (fun v : ℝ => g v / (Complex.I * v)) = g *
      (fun v : ℝ => (Complex.I * v)⁻¹) := by funext v; exact div_eq_mul_inv _ _
  rw [he]
  exact hg.mul_right

private theorem exp_kernel_nonzero (v : ℝ) (hv : v ≠ 0) :
    1 - Complex.exp (-2 * (v : ℂ)) ≠ 0 := by
  have he : -2 * (v : ℂ) = ((-2 * v : ℝ) : ℂ) := by push_cast; ring
  rw [he, ← Complex.ofReal_exp]
  intro h
  have hreal := congrArg Complex.re h
  simp only [Complex.sub_re, Complex.one_re, Complex.ofReal_re, Complex.zero_re] at hreal
  have hexp : Real.exp (-2 * v) = Real.exp 0 := by rw [Real.exp_zero]; linarith
  have harg := Real.exp_injective hexp
  apply hv
  linarith

private theorem kernel_integrable (g : ℝ → ℂ) (hgc : HasCompactSupport g)
    (hg : Continuous g) (h0 : 0 ∉ tsupport g) :
    Integrable (fun v : ℝ => g v * Complex.exp (-(v : ℂ) / 2) /
      (1 - Complex.exp (-2 * (v : ℂ)))) := by
  have hc : HasCompactSupport (fun v : ℝ => g v * Complex.exp (-(v : ℂ) / 2) /
      (1 - Complex.exp (-2 * (v : ℂ)))) := by
    have he : (fun v : ℝ => g v * Complex.exp (-(v : ℂ) / 2) /
        (1 - Complex.exp (-2 * (v : ℂ)))) =
        (g * (fun v : ℝ => Complex.exp (-(v : ℂ) / 2))) *
          (fun v : ℝ => (1 - Complex.exp (-2 * (v : ℂ)))⁻¹) := by
      funext v; exact div_eq_mul_inv _ _
    rw [he]
    exact hgc.mul_right.mul_right
  have ht : Continuous (fun v : ℝ => g v * Complex.exp (-(v : ℂ) / 2) /
      (1 - Complex.exp (-2 * (v : ℂ)))) := by
    rw [continuous_iff_continuousAt]
    intro v
    by_cases hv : v = 0
    · subst v
      have he : (fun v : ℝ => g v * Complex.exp (-(v : ℂ) / 2) /
          (1 - Complex.exp (-2 * (v : ℂ)))) =ᶠ[𝓝 0] (fun _ => (0 : ℂ)) := by
        filter_upwards [(isClosed_tsupport g).isOpen_compl.mem_nhds h0] with x hx
        simp [image_eq_zero_of_notMem_tsupport hx]
      exact continuousAt_const.congr_of_eventuallyEq he
    · exact (hg.continuousAt.mul (by fun_prop)).div (by fun_prop) (exp_kernel_nonzero v hv)
  exact ht.integrable_of_hasCompactSupport hc

private theorem kernel_rational_identity (z a : ℂ) (hz : z ≠ 0) (hsq : z ^ 2 - 1 ≠ 0) :
    a - a / (1 - (z ^ 2)⁻¹) = -z * (a / (z ^ 3 - z)) := by
  have hc : z ^ 3 - z ≠ 0 := by
    rw [show z ^ 3 - z = z * (z ^ 2 - 1) by ring]
    exact mul_ne_zero hz hsq
  have hd : 1 - (z ^ 2)⁻¹ ≠ 0 := by
    intro h
    have hh : z ^ 2 = 1 := by
      have hmul := congrArg (fun w : ℂ => w * z ^ 2) h
      simp only [sub_mul, one_mul, inv_mul_cancel₀ (pow_ne_zero _ hz), zero_mul] at hmul
      linear_combination hmul
    exact hsq (by rw [hh]; ring)
  field_simp [hz, hsq, hc, hd] <;> ring


private theorem archTerm_positive_support (g : ℝ → ℂ)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hc : HasCompactSupport g)
    (hsupp : tsupport g ⊆ Ioi 0) :
    ConnesRZ.archTerm g = -(∫ v : ℝ in Ioi 0,
      g v * Complex.exp (-(v : ℂ) / 2) / (1 - Complex.exp (-2 * (v : ℂ)))) := by
  have h0 : 0 ∉ tsupport g := by
    intro h
    have hh := hsupp h
    change (0 : ℝ) < 0 at hh
    exact (lt_irrefl (0 : ℝ)) hh
  let G : SchwartzMap ℝ ℂ := hc.toSchwartzMap hg
  let H : SchwartzMap ℝ ℂ := (divide_compact g hc).toSchwartzMap (divide_smooth g hg h0)
  have hrel : ∀ v : ℝ, Complex.I * v * H v = G v := by
    intro v
    change Complex.I * v * (g v / (Complex.I * v)) = g v
    by_cases hv : v = 0
    · subst v
      simp [image_eq_zero_of_notMem_tsupport h0]
    · field_simp [Complex.I_ne_zero, Complex.ofReal_ne_zero.mpr hv]
  have hs : Function.support (fun v : ℝ => H v) ⊆ Ioi 0 := by
    intro v hv
    have hgv : g v ≠ 0 := by intro hz; exact hv (by change g v / (Complex.I * v) = 0; simp [hz])
    exact hsupp (subset_tsupport _ hgv)
  exact TaoFivePrimes.PhysicalConversion.archTerm_of_division G H hrel hs

private theorem main_dictionary (eta : ℝ → ℂ)
    (hsupp : ∀ u, eta u ≠ 0 → 2 ≤ u) :
    ConnesRZ.mellinHat (logTest eta) 1 = ∫ u : ℝ, eta u := by
  rw [mellin_dictionary eta hsupp]
  simp

private theorem pole_arch_dictionary (eta : ℝ → ℂ)
    (heta : ContDiff ℝ (⊤ : ℕ∞) eta) (hc : HasCompactSupport eta)
    (hsupp : ∀ u, eta u ≠ 0 → 2 ≤ u) :
    ConnesRZ.mellinHat (logTest eta) 0 + ConnesRZ.archTerm (logTest eta) =
      -(∫ u : ℝ, eta u / (((u ^ 3 - u : ℝ) : ℂ))) := by
  let g := logTest eta
  let p : ℝ → ℂ := fun v => g v * Complex.exp (-(v : ℂ) / 2)
  let k : ℝ → ℂ := fun v => p v / (1 - Complex.exp (-2 * (v : ℂ)))
  let f : ℝ → ℂ := fun u => eta u / ((u ^ 3 - u : ℝ) : ℂ)
  have h0 : 0 ∉ tsupport g := by
    intro h
    have hh := logTest_pos_support eta hsupp h
    change (0 : ℝ) < 0 at hh
    exact (lt_irrefl (0 : ℝ)) hh
  have hp : Integrable p := by
    exact ((logTest_smooth eta heta).continuous.mul (by fun_prop)).integrable_of_hasCompactSupport
      ((logTest_compact eta hc hsupp).mul_right)
  have hk : Integrable k := kernel_integrable g (logTest_compact eta hc hsupp)
    (logTest_smooth eta heta).continuous h0
  have hps : Function.support p ⊆ Ioi 0 := by
    intro v hv
    have hgv : g v ≠ 0 := by intro hz; exact hv (by simp [p, hz])
    exact logTest_pos_support eta hsupp (subset_tsupport _ hgv)
  have hM : ConnesRZ.mellinHat g 0 = ∫ v : ℝ in Ioi 0, p v := by
    unfold ConnesRZ.mellinHat
    rw [← integral_supported p (Ioi 0) measurableSet_Ioi hps]
    congr 1
    funext v
    dsimp [p]
    congr 1
    congr 1
    ring
  have hA : ConnesRZ.archTerm g = -(∫ v : ℝ in Ioi 0, k v) :=
    archTerm_positive_support g (logTest_smooth eta heta) (logTest_compact eta hc hsupp)
      (logTest_pos_support eta hsupp)
  have hfn : ∀ v : ℝ, 0 < v → p v - k v = -(Real.exp v : ℂ) * f (Real.exp v) := by
    intro v hv
    have hE : (Real.exp v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_pos v).ne'
    have hneg : Complex.exp (-2 * (v : ℂ)) = ((Real.exp v : ℂ) ^ 2)⁻¹ := by
      have he2 : Complex.exp (2 * (v : ℂ)) = Complex.exp (v : ℂ) ^ 2 := by
        simpa using Complex.exp_nat_mul (v : ℂ) 2
      rw [show -2 * (v : ℂ) = -(2 * (v : ℂ)) by ring, Complex.exp_neg,
        he2, ← Complex.ofReal_exp]
    have hweight : Complex.exp ((v : ℂ) / 2) * Complex.exp (-(v : ℂ) / 2) = 1 := by
      rw [← Complex.exp_add, show (v : ℂ) / 2 + -(v : ℂ) / 2 = 0 by ring, Complex.exp_zero]
    have hpv : p v = eta (Real.exp v) := by
      dsimp [p, g, logTest]
      calc
        _ = (Complex.exp ((v : ℂ) / 2) * Complex.exp (-(v : ℂ) / 2)) * eta (Real.exp v) := by ring
        _ = _ := by rw [hweight, one_mul]
    change p v - p v / (1 - Complex.exp (-2 * (v : ℂ))) = _
    rw [hpv, hneg]
    have hsq : (Real.exp v : ℂ) ^ 2 - 1 ≠ 0 := by
      exact_mod_cast (show Real.exp v ^ 2 - 1 ≠ 0 by nlinarith [Real.one_lt_exp_iff.mpr hv])
    dsimp [f]
    push_cast
    simpa only [Complex.ofReal_exp] using kernel_rational_identity (Real.exp v : ℂ)
      (eta (Real.exp v)) hE hsq
  have hf : Function.support f ⊆ Ioi 1 := by
    intro u hu
    have he : eta u ≠ 0 := by intro hz; exact hu (by simp [f, hz])
    exact lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) (hsupp _ he)
  have hi : (∫ v : ℝ in Ioi 0, p v - k v) = -(∫ u : ℝ, f u) := by
    calc
      _ = ∫ v : ℝ in Ioi 0, -(Real.exp v : ℂ) * f (Real.exp v) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro v hv; exact hfn v hv
      _ = -(∫ v : ℝ in Ioi 0, (Real.exp v : ℂ) * f (Real.exp v)) := by
        simp_rw [neg_mul]; exact integral_neg _
      _ = -(∫ u : ℝ in Ioi 1, f u) := by rw [change_exp]
      _ = _ := by rw [← integral_supported f (Ioi 1) measurableSet_Ioi hf]
  rw [hM, hA, ← sub_eq_add_neg, ← integral_sub hp.integrableOn hk.integrableOn, hi]

private theorem correction_integrable (eta : ℝ → ℂ) (heta : Continuous eta)
    (hc : HasCompactSupport eta) (hsupp : ∀ u, eta u ≠ 0 → 2 ≤ u) :
    Integrable (fun u : ℝ => eta u / ((u ^ 3 - u : ℝ) : ℂ)) := by
  have hcomp : HasCompactSupport (fun u : ℝ => eta u / ((u ^ 3 - u : ℝ) : ℂ)) := by
    have he : (fun u : ℝ => eta u / ((u ^ 3 - u : ℝ) : ℂ)) =
        eta * (fun u : ℝ => (((u ^ 3 - u : ℝ) : ℂ))⁻¹) := by
      funext u; exact div_eq_mul_inv _ _
    rw [he]
    exact hc.mul_right
  have hcont : Continuous (fun u : ℝ => eta u / ((u ^ 3 - u : ℝ) : ℂ)) := by
    rw [continuous_iff_continuousAt]
    intro u
    by_cases hu : u < 2
    · have he : (fun u : ℝ => eta u / ((u ^ 3 - u : ℝ) : ℂ)) =ᶠ[𝓝 u] (fun _ => (0 : ℂ)) := by
        filter_upwards [isOpen_Iio.mem_nhds hu] with v hv
        have hveta : eta v = 0 := by
          by_contra hn
          exact (not_lt.mpr (hsupp _ hn)) hv
        simp [hveta]
      exact continuousAt_const.congr_of_eventuallyEq he
    · have hup : 2 ≤ u := not_lt.mp hu
      have hd : ((u ^ 3 - u : ℝ) : ℂ) ≠ 0 := by
        apply Complex.ofReal_ne_zero.mpr
        rw [show u ^ 3 - u = u * (u - 1) * (u + 1) by ring]
        exact mul_ne_zero (mul_ne_zero (by linarith) (by linarith)) (by linarith)
      exact heta.continuousAt.div (by fun_prop) hd
  exact hcont.integrable_of_hasCompactSupport hcomp

end TaoFivePrimes.Prop71

open TaoFivePrimes.Prop71

theorem solution (eta : ℝ → ℂ) (hsmooth : ContDiff ℝ (⊤ : ℕ∞) eta)
    (hcompact : HasCompactSupport eta) (hsupp : ∀ u, eta u ≠ 0 → 2 ≤ u) :
    HasSum (fun rho : {s : ℂ // ConnesRZ.IsCriticalZero s} =>
      (analyticOrderNatAt riemannZeta rho.val : ℂ) *
        (∫ u : ℝ, eta u * (u : ℂ) ^ (rho.val - 1)))
      ((∫ u : ℝ, ((1 : ℂ) - 1 / (((u ^ 3 - u : ℝ) : ℂ))) * eta u) -
        (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) * eta n)) := by
  let g := logTest eta
  have hC := ConnesRZ.explicit_formula_C2 g
    ((logTest_smooth eta hsmooth).of_le (WithTop.coe_le_coe.mpr le_top))
    (logTest_compact eta hcompact hsupp)
  have hPole := pole_arch_dictionary eta hsmooth hcompact hsupp
  have hPrime := prime_dictionary eta hsupp
  have hMain := main_dictionary eta hsupp
  have heta : Integrable eta := hsmooth.continuous.integrable_of_hasCompactSupport hcompact
  have hJ := correction_integrable eta hsmooth.continuous hcompact hsupp
  have hWeighted : (∫ u : ℝ, ((1 : ℂ) - 1 / (((u ^ 3 - u : ℝ) : ℂ))) * eta u) =
      (∫ u : ℝ, eta u) - (∫ u : ℝ, eta u / (((u ^ 3 - u : ℝ) : ℂ))) := by
    rw [← integral_sub heta hJ]
    apply integral_congr_ae
    filter_upwards [] with u
    ring
  convert hC using 1
  · funext rho
    rw [mellin_dictionary eta hsupp]
    rfl
  · unfold ConnesRZ.weilDistribution
    rw [hWeighted, hPrime, hMain]
    linear_combination -hPole
