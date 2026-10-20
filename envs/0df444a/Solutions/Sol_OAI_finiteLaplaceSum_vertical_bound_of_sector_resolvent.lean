-- Prove2me | solution 1 for OAI.finiteLaplaceSum_vertical_bound_of_sector_resolvent
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T22:12:30.026871+00:00
-- url     : https://prove2.me/submissions/be74f557-4252-4fdf-ab51-697415559516

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/FiniteContour.lean:L363-L473
-- (upload_full_project.md Phase 4): solution for node OAI.finiteLaplaceSum_vertical_bound_of_sector_resolvent. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_Cotype
import Definitions.Def_OAI_Analysis_Cotype_ComplexDualLift
import Definitions.Def_OAI_Analysis_Cotype_Cube
import Definitions.Def_OAI_Analysis_Cotype_Target
import Definitions.Def_OAI_Analysis_Cotype_Moments
import Definitions.Def_OAI_Analysis_Cotype_Fourier
import Definitions.Def_OAI_Analysis_Cotype_ScalarWalsh
import Definitions.Def_OAI_Analysis_Cotype_VectorWalsh
import Definitions.Def_OAI_Analysis_Cotype_WalshNorm
import Definitions.Def_OAI_Analysis_Cotype_WalshCoordinates
import Definitions.Def_OAI_Analysis_Cotype_WalshDuality
import Definitions.Def_OAI_Analysis_Cotype_CubeNoise
import Definitions.Def_OAI_Analysis_Cotype_ProjectionProducts
import Definitions.Def_OAI_Analysis_Cotype_UniformL1
import Definitions.Def_OAI_Analysis_Cotype_BConvexity
import Definitions.Def_OAI_Analysis_Cotype_ProjectionAverages
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSemigroup
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSemigroupBasics
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSpectrum
import Definitions.Def_OAI_Analysis_Cotype_ComplexProjectionPolynomial
import Definitions.Def_OAI_Analysis_Cotype_ComplexProjectionSpectrum
import Definitions.Def_OAI_Analysis_Cotype_ProjectionGenerator
import Definitions.Def_OAI_Analysis_Cotype_PowerGapInverse
import Definitions.Def_OAI_Analysis_Cotype_ExponentialIntegral
import Definitions.Def_OAI_Analysis_Cotype_ProjectionResolvent
import Definitions.Def_OAI_Analysis_Cotype_SectorResolvent
import Definitions.Def_OAI_Analysis_Cotype_FiniteContour

-- ---- from OAI.Analysis.Cotype.FiniteContour ----
namespace OAI

open Complex Set MeasureTheory Filter
open scoped BigOperators Interval Topology

namespace FiniteContour

theorem resolvent_differentiableAt {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {ι : Type*} [Fintype ι] (lam : ι → ℝ) (v : ι → E)
    {z : ℂ} (hz : ∀ i, z ≠ (lam i : ℂ)) :
    DifferentiableAt ℂ (resolvent lam v) z := by
  classical
  apply DifferentiableAt.fun_sum
  intro i _
  have hd : DifferentiableAt ℂ (fun q : ℂ => (q - (lam i : ℂ))⁻¹) z :=
    (differentiableAt_id.sub_const (lam i : ℂ)).inv (sub_ne_zero.mpr (hz i))
  exact hd.smul_const (v i)

theorem scalar_cauchy (w : ℂ) (l R : ℝ) (hl : ‖(l : ℂ)‖ < R) :
    (∮ z in C(0, R), (z - (l : ℂ))⁻¹ * exp (-(w * z))) =
      (2 * Real.pi * I) * exp (-(w * (l : ℂ))) := by
  have hd : Differentiable ℂ (fun z : ℂ => exp (-(w * z))) :=
    differentiable_exp.comp (differentiable_id.const_mul w).neg
  simpa only [smul_eq_mul] using hd.differentiableOn.circleIntegral_sub_inv_smul
    (show (l : ℂ) ∈ Metric.ball (0 : ℂ) R by simpa using hl)

theorem finite_cauchy {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {ι : Type*} [Fintype ι] (lam : ι → ℝ) (v : ι → E)
    (w : ℂ) {R : ℝ} (hR : 0 < R) (hl : ∀ i, ‖(lam i : ℂ)‖ < R) :
    (∮ z in C(0, R), exp (-(w * z)) • resolvent lam v z) =
      (2 * Real.pi * I : ℂ) • laplace lam v w := by
  classical
  have hi (i : ι) : CircleIntegrable
      (fun z : ℂ => ((z - (lam i : ℂ))⁻¹ * exp (-(w * z))) • v i) 0 R := by
    apply ContinuousOn.circleIntegrable hR.le
    apply ContinuousOn.smul _ continuousOn_const
    apply ContinuousOn.mul
    · apply ContinuousOn.inv₀ (continuousOn_id.sub continuousOn_const)
      intro z hz he
      have he' : z = (lam i : ℂ) := sub_eq_zero.mp he
      have : ‖(lam i : ℂ)‖ = R := by simpa [he'] using hz
      exact (ne_of_lt (hl i)) this
    · exact (continuous_exp.comp ((continuous_const.mul continuous_id).neg)).continuousOn
  simp only [resolvent, laplace, Finset.smul_sum]
  simp_rw [smul_smul, mul_comm (exp _) (_ : ℂ)]
  rw [circleIntegral.integral_fun_sum (fun i _ => hi i)]
  simp_rw [circleIntegral.integral_smul_const, scalar_cauchy w _ R (hl _)]

theorem logKernel_differentiableAt {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {ι : Type*} [Fintype ι] (lam : ι → ℝ) (v : ι → E)
    (w : ℂ) {q : ℂ} (hq : ∀ i, exp q ≠ (lam i : ℂ)) :
    DifferentiableAt ℂ (logKernel lam v w) q := by
  exact (differentiable_exp.differentiableAt.mul
    ((differentiable_exp.comp (differentiable_exp.const_mul w).neg).differentiableAt)).smul
    ((resolvent_differentiableAt lam v hq).comp q differentiable_exp.differentiableAt)

theorem log_rectangle {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {ι : Type*} [Fintype ι] (lam : ι → ℝ) (v : ι → E)
    (w : ℂ) (b alpha beta : ℝ)
    (hp : ∀ q : ℂ, q.re ∈ Set.uIcc 0 b → q.im ∈ Set.uIcc alpha beta →
      ∀ i, exp q ≠ (lam i : ℂ)) :
    (∫ x : ℝ in 0..b, logKernel lam v w (x + alpha * I)) -
      (∫ x : ℝ in 0..b, logKernel lam v w (x + beta * I)) +
      I • (∫ y : ℝ in alpha..beta, logKernel lam v w (b + y * I)) -
      I • (∫ y : ℝ in alpha..beta, logKernel lam v w (y * I)) = 0 := by
  have hd : DifferentiableOn ℂ (logKernel lam v w)
      (Set.uIcc 0 b ×ℂ Set.uIcc alpha beta) := by
    intro q hq
    exact (logKernel_differentiableAt lam v w (hp q hq.1 hq.2)).differentiableWithinAt
  simpa using Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    (logKernel lam v w) (Complex.mk 0 alpha) (Complex.mk b beta) hd

theorem vertical_mul_re_lower {c T tau : ℝ} (hc : 0 < c)
    (hT : T * c = Real.pi + 1) (htau : |tau| ≤ Real.pi)
    {z : ℂ} (hz : c * ‖z‖ ≤ z.re) :
    ‖z‖ ≤ (((T : ℂ) + (tau : ℂ) * I) * z).re := by
  have hTpos : 0 < T := (mul_pos_iff_of_pos_right hc).mp (by rw [hT]; positivity)
  have him : tau * z.im ≤ Real.pi * ‖z‖ := calc
    tau * z.im ≤ |tau * z.im| := le_abs_self _
    _ = |tau| * |z.im| := abs_mul _ _
    _ ≤ Real.pi * ‖z‖ := mul_le_mul htau (abs_im_le_norm z) (abs_nonneg _) Real.pi_pos.le
  have hre := mul_le_mul_of_nonneg_left hz hTpos.le
  rw [← mul_assoc, hT] at hre
  simp only [mul_re, add_re, add_im, ofReal_re, ofReal_im, mul_im, I_re, I_im,
    mul_zero, mul_one, sub_zero, zero_add, add_zero] at *
  nlinarith

theorem exponential_decay {c T tau : ℝ} (hc : 0 < c)
    (hT : T * c = Real.pi + 1) (htau : |tau| ≤ Real.pi)
    {z : ℂ} (hz : c * ‖z‖ ≤ z.re) :
    ‖exp (-(((T : ℂ) + (tau : ℂ) * I) * z))‖ ≤ Real.exp (-‖z‖) := by
  rw [norm_exp, neg_re]
  exact Real.exp_le_exp.mpr (neg_le_neg (vertical_mul_re_lower hc hT htau hz))

theorem weighted_resolvent_bound {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {ι : Type*} [Fintype ι] (lam : ι → ℝ) (v : ι → E)
    {M : ℝ} (_hM : 0 ≤ M) {z w : ℂ} (hz : z ≠ 0)
    (hr : ‖resolvent lam v z‖ ≤ M / ‖z‖) :
    ‖(z * exp (-(w * z))) • resolvent lam v z‖ ≤ M * ‖exp (-(w * z))‖ := by
  rw [norm_smul, norm_mul]
  calc
    ‖z‖ * ‖exp (-(w * z))‖ * ‖resolvent lam v z‖
        ≤ ‖z‖ * ‖exp (-(w * z))‖ * (M / ‖z‖) :=
      mul_le_mul_of_nonneg_left hr (by positivity)
    _ = M * ‖exp (-(w * z))‖ := by field_simp [norm_ne_zero_iff.mpr hz]

theorem upper_arc_sector {a theta y : ℝ} (ha : 0 ≤ a) (htheta : 0 ≤ theta)
    (htheta' : theta ≤ Real.pi / 2)
    (hslope : Real.cos theta ≤ a * Real.sin theta)
    (hy : theta ≤ y) (hy' : y ≤ Real.pi) :
    Real.cos y ≤ a * |Real.sin y| := by
  by_cases h : y ≤ Real.pi / 2
  · have hcos := Real.cos_le_cos_of_nonneg_of_le_pi htheta hy' hy
    have hsin := Real.sin_le_sin_of_le_of_le_pi_div_two
      (by linarith [Real.pi_pos] : -(Real.pi / 2) ≤ theta) h hy
    exact hcos.trans (hslope.trans ((mul_le_mul_of_nonneg_left hsin ha).trans
      (mul_le_mul_of_nonneg_left (le_abs_self _) ha)))
  · exact (Real.cos_nonpos_of_pi_div_two_le_of_le (le_of_not_ge h)
      (by linarith [Real.pi_pos])).trans (mul_nonneg ha (abs_nonneg _))

theorem left_arc_sector {a theta y : ℝ} (ha : 0 ≤ a) (htheta : 0 ≤ theta)
    (htheta' : theta ≤ Real.pi / 2)
    (hslope : Real.cos theta ≤ a * Real.sin theta)
    (hy : theta ≤ y) (hy' : y ≤ 2 * Real.pi - theta) :
    Real.cos y ≤ a * |Real.sin y| := by
  by_cases h : y ≤ Real.pi
  · exact upper_arc_sector ha htheta htheta' hslope hy h
  · have hh := upper_arc_sector ha htheta htheta' hslope
      (y := 2 * Real.pi - y) (by linarith) (by linarith)
    simpa only [Real.cos_two_pi_sub, Real.sin_two_pi_sub, abs_neg] using hh

theorem exp_sector {a theta : ℝ} (ha : 0 ≤ a) (htheta : 0 ≤ theta)
    (htheta' : theta ≤ Real.pi / 2)
    (hslope : Real.cos theta ≤ a * Real.sin theta)
    {q : ℂ} (hq : q.im ∈ Set.Icc theta (2 * Real.pi - theta)) :
    (exp q).re ≤ a * |(exp q).im| := by
  have hh := mul_le_mul_of_nonneg_left
    (left_arc_sector ha htheta htheta' hslope hq.1 hq.2) (Real.exp_pos q.re).le
  simpa only [exp_re, exp_im, abs_mul, abs_of_pos (Real.exp_pos q.re),
    mul_left_comm] using hh

theorem sector_ne_nonneg {a : ℝ} {z : ℂ} (hz : z ≠ 0)
    (hs : z.re ≤ a * |z.im|) {l : ℝ} (hl : 0 ≤ l) : z ≠ (l : ℂ) := by
  intro he
  subst z
  have : l = 0 := by simpa using le_antisymm (by simpa using hs) hl
  simp [this] at hz

theorem angle_exists {a : ℝ} (ha : 0 < a) :
    ∃ theta : ℝ, 0 < theta ∧ theta < Real.pi / 2 ∧
      0 < Real.cos theta ∧ Real.cos theta ≤ a * Real.sin theta := by
  refine ⟨Real.arctan (2 / a), Real.arctan_pos.mpr (by positivity),
    Real.arctan_lt_pi_div_two _, Real.cos_arctan_pos _, ?_⟩
  rw [Real.cos_arctan, Real.sin_arctan]
  calc
    1 / Real.sqrt (1 + (2 / a) ^ 2) ≤ 2 / Real.sqrt (1 + (2 / a) ^ 2) :=
      div_le_div_of_nonneg_right (by norm_num) (Real.sqrt_nonneg _)
    _ = a * ((2 / a) / Real.sqrt (1 + (2 / a) ^ 2)) := by field_simp

theorem fixed_arc_exp_bound {T tau : ℝ} (hT : 0 ≤ T) (htau : |tau| ≤ Real.pi)
    {z : ℂ} (hz : ‖z‖ = 1) :
    ‖exp (-(((T : ℂ) + (tau : ℂ) * I) * z))‖ ≤ Real.exp (T + Real.pi) := by
  rw [norm_exp]
  apply Real.exp_le_exp.mpr
  calc
    (-(((T : ℂ) + (tau : ℂ) * I) * z)).re ≤
        ‖-(((T : ℂ) + (tau : ℂ) * I) * z)‖ := re_le_norm _
    _ = ‖(T : ℂ) + (tau : ℂ) * I‖ := by rw [norm_neg, norm_mul, hz, mul_one]
    _ ≤ ‖(T : ℂ)‖ + ‖(tau : ℂ) * I‖ := norm_add_le _ _
    _ ≤ T + Real.pi := by simpa [norm_mul, abs_of_nonneg hT] using add_le_add_left htau T

theorem logKernel_circle {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {ι : Type*} [Fintype ι] (lam : ι → ℝ) (v : ι → E)
    (w : ℂ) (b : ℝ) :
    (∮ z in C(0, Real.exp b), exp (-(w * z)) • resolvent lam v z) =
      I • (∫ y : ℝ in 0..2 * Real.pi, logKernel lam v w (b + y * I)) := by
  rw [← intervalIntegral.integral_smul]
  unfold circleIntegral
  apply intervalIntegral.integral_congr
  intro y _
  simp only [logKernel, deriv_circleMap, circleMap, zero_add, ofReal_exp,
    exp_add, smul_smul]
  congr 1
  ring

theorem logKernel_ray_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {ι : Type*} [Fintype ι] (lam : ι → ℝ) (v : ι → E)
    {a M theta T tau : ℝ} (hM : 0 ≤ M) (hc : 0 < Real.cos theta)
    (hT : T * Real.cos theta = Real.pi + 1) (htau : |tau| ≤ Real.pi)
    (hr : ∀ z : ℂ, z ≠ 0 → z.re ≤ a * |z.im| → ‖resolvent lam v z‖ ≤ M / ‖z‖)
    {y : ℝ} (hs : Real.cos y ≤ a * |Real.sin y|) (hy : Real.cos y = Real.cos theta)
    (x : ℝ) :
    ‖logKernel lam v ((T : ℂ) + (tau : ℂ) * I) (x + y * I)‖ ≤ M * Real.exp (-x) := by
  let z : ℂ := exp ((x : ℂ) + (y : ℂ) * I)
  have hz : z ≠ 0 := exp_ne_zero _
  have hzn : ‖z‖ = Real.exp x := by simp [z, norm_exp]
  have hzs : z.re ≤ a * |z.im| := by
    simpa [z, exp_re, exp_im, abs_mul, abs_of_pos (Real.exp_pos x), mul_left_comm] using
      mul_le_mul_of_nonneg_left hs (Real.exp_pos x).le
  have hzr : Real.cos theta * ‖z‖ ≤ z.re := by
    simp [z, norm_exp, exp_re, hy, mul_comm]
  calc
    ‖logKernel lam v ((T : ℂ) + (tau : ℂ) * I) (x + y * I)‖
        ≤ M * ‖exp (-(((T : ℂ) + (tau : ℂ) * I) * z))‖ :=
      weighted_resolvent_bound lam v hM hz (hr z hz hzs)
    _ ≤ M * Real.exp (-‖z‖) := mul_le_mul_of_nonneg_left (exponential_decay hc hT htau hzr) hM
    _ ≤ M * Real.exp (-x) := by
      rw [hzn]
      apply mul_le_mul_of_nonneg_left _ hM
      exact Real.exp_le_exp.mpr (by linarith [Real.add_one_le_exp x])

theorem logKernel_fixed_arc_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {ι : Type*} [Fintype ι] (lam : ι → ℝ) (v : ι → E)
    {a M T tau : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T) (htau : |tau| ≤ Real.pi)
    (hr : ∀ z : ℂ, z ≠ 0 → z.re ≤ a * |z.im| → ‖resolvent lam v z‖ ≤ M / ‖z‖)
    {y : ℝ} (hs : Real.cos y ≤ a * |Real.sin y|) :
    ‖logKernel lam v ((T : ℂ) + (tau : ℂ) * I) (y * I)‖ ≤ M * Real.exp (T + Real.pi) := by
  let z : ℂ := exp ((y : ℂ) * I)
  have hz : z ≠ 0 := exp_ne_zero _
  have hzn : ‖z‖ = 1 := by simp [z, norm_exp]
  have hzs : z.re ≤ a * |z.im| := by simpa [z, exp_re, exp_im] using hs
  exact (weighted_resolvent_bound lam v hM hz (hr z hz hzs)).trans
    (mul_le_mul_of_nonneg_left (fixed_arc_exp_bound hT htau hzn) hM)

theorem ray_integral_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {M b : ℝ} (hM : 0 ≤ M) (hb : 0 ≤ b)
    (hf : ∀ x, ‖f x‖ ≤ M * Real.exp (-x)) : ‖∫ x in 0..b, f x‖ ≤ M := by
  have hh : ‖∫ x in 0..b, f x‖ ≤ ∫ x in 0..b, M * Real.exp (-x) :=
    intervalIntegral.norm_integral_le_of_norm_le hb
      (Filter.Eventually.of_forall (fun x _ => hf x))
      ((by fun_prop : Continuous (fun x : ℝ => M * Real.exp (-x))).intervalIntegrable _ _)
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_neg, integral_exp] at hh
  simp only [neg_zero, Real.exp_zero] at hh
  nlinarith [Real.exp_pos (-b)]

theorem resolvent_radius_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {ι : Type*} [Fintype ι] (lam : ι → ℝ) (v : ι → E)
    {R : ℝ} (hR : 0 < R) (hl : ∀ i, ‖(lam i : ℂ)‖ ≤ R / 2)
    {z : ℂ} (hz : ‖z‖ = R) : ‖resolvent lam v z‖ ≤ (2 / R) * ∑ i, ‖v i‖ := by
  classical
  calc
    ‖resolvent lam v z‖ ≤ ∑ i, ‖(z - (lam i : ℂ))⁻¹ • v i‖ := norm_sum_le _ _
    _ ≤ ∑ i, (2 / R) * ‖v i‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul, norm_inv]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      have hn := norm_sub_norm_le z (lam i : ℂ)
      rw [hz] at hn
      have hd : R / 2 ≤ ‖z - (lam i : ℂ)‖ := by linarith [hl i]
      have hdpos : 0 < ‖z - (lam i : ℂ)‖ := lt_of_lt_of_le (by positivity) hd
      rw [inv_eq_one_div, div_le_div_iff₀ hdpos hR]
      linarith
    _ = (2 / R) * ∑ i, ‖v i‖ := (Finset.mul_sum _ _ _).symm

theorem logKernel_outer_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {ι : Type*} [Fintype ι] (lam : ι → ℝ) (v : ι → E)
    {theta T tau b : ℝ} (hc : 0 < Real.cos theta)
    (hT : T * Real.cos theta = Real.pi + 1) (htau : |tau| ≤ Real.pi)
    (hl : ∀ i, ‖(lam i : ℂ)‖ ≤ Real.exp b / 2)
    {y : ℝ} (hy : Real.cos theta ≤ Real.cos y) :
    ‖logKernel lam v ((T : ℂ) + (tau : ℂ) * I) (b + y * I)‖ ≤
      (2 * ∑ i, ‖v i‖) * Real.exp (-Real.exp b) := by
  let z : ℂ := exp ((b : ℂ) + (y : ℂ) * I)
  have hzn : ‖z‖ = Real.exp b := by simp [z, norm_exp]
  have hzr : Real.cos theta * ‖z‖ ≤ z.re := by
    simpa [z, norm_exp, exp_re, mul_comm] using
      mul_le_mul_of_nonneg_left hy (Real.exp_pos b).le
  have hr : ‖resolvent lam v z‖ ≤ (2 * ∑ i, ‖v i‖) / ‖z‖ := by
    rw [hzn]
    convert resolvent_radius_bound lam v (Real.exp_pos b) hl hzn using 1
    ring
  exact (weighted_resolvent_bound lam v (by positivity) (exp_ne_zero _) hr).trans
    (by
      have hh := mul_le_mul_of_nonneg_left (exponential_decay hc hT htau hzr)
        (by positivity : 0 ≤ 2 * ∑ i, ‖v i‖)
      simpa [hzn] using hh)

theorem logKernel_horizontal_continuous {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {ι : Type*} [Fintype ι] (lam : ι → ℝ) (v : ι → E)
    (w : ℂ) {b : ℝ} (hl : ∀ i, ‖(lam i : ℂ)‖ < Real.exp b) :
    Continuous (fun y : ℝ => logKernel lam v w (b + y * I)) := by
  apply continuous_iff_continuousAt.mpr
  intro y
  have hp : ∀ i, exp ((b : ℂ) + (y : ℂ) * I) ≠ (lam i : ℂ) := by
    intro i he
    have he' := congrArg norm he
    simp only [norm_exp, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
      mul_zero, zero_mul, sub_self, add_zero] at he'
    linarith [hl i]
  exact ContinuousAt.comp (g := logKernel lam v w)
    (f := fun t : ℝ => (b : ℂ) + (t : ℂ) * I)
    (logKernel_differentiableAt lam v w hp).continuousAt
    (by fun_prop : ContinuousAt (fun y : ℝ => (b : ℂ) + (y : ℂ) * I) y)

theorem finite_truncated_contour {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {ι : Type*} [Fintype ι] (lam : ι → ℝ) (v : ι → E)
    (w : ℂ) {a theta b : ℝ} (ha : 0 ≤ a) (htheta : 0 ≤ theta)
    (htheta' : theta ≤ Real.pi / 2) (hslope : Real.cos theta ≤ a * Real.sin theta)
    (hl0 : ∀ i, 0 ≤ lam i) (hl : ∀ i, ‖(lam i : ℂ)‖ < Real.exp b) :
    (2 * Real.pi * I : ℂ) • laplace lam v w =
      I • (∫ y : ℝ in 0..theta, logKernel lam v w (b + y * I)) +
      I • (∫ y : ℝ in theta..2 * Real.pi - theta, logKernel lam v w (y * I)) -
      (∫ x : ℝ in 0..b, logKernel lam v w (x + theta * I)) +
      (∫ x : ℝ in 0..b, logKernel lam v w (x + ((2 * Real.pi - theta : ℝ) : ℂ) * I)) +
      I • (∫ y : ℝ in 2 * Real.pi - theta..2 * Real.pi,
        logKernel lam v w (b + y * I)) := by
  have horder : theta ≤ 2 * Real.pi - theta := by linarith [Real.pi_pos]
  have hrect := log_rectangle lam v w b theta (2 * Real.pi - theta) (by
    intro q _ hq i
    rw [Set.uIcc_of_le horder] at hq
    exact sector_ne_nonneg (exp_ne_zero q)
      (exp_sector ha htheta htheta' hslope hq) (hl0 i))
  have hleft : I • (∫ y : ℝ in theta..2 * Real.pi - theta,
        logKernel lam v w (b + y * I)) =
      I • (∫ y : ℝ in theta..2 * Real.pi - theta, logKernel lam v w (y * I)) -
      (∫ x : ℝ in 0..b, logKernel lam v w (x + theta * I)) +
      (∫ x : ℝ in 0..b, logKernel lam v w (x + ((2 * Real.pi - theta : ℝ) : ℂ) * I)) := by
    have hh := eq_sub_of_add_eq' (sub_eq_zero.mp hrect)
    calc
      _ = _ := hh
      _ = _ := by abel
  have hi := (logKernel_horizontal_continuous lam v w hl).intervalIntegrable (μ := volume)
  rw [← finite_cauchy lam v w (Real.exp_pos b) hl, logKernel_circle]
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi 0 (2 * Real.pi - theta))
    (hi (2 * Real.pi - theta) (2 * Real.pi))]
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi 0 theta)
    (hi theta (2 * Real.pi - theta)), smul_add, smul_add, hleft]
  abel

theorem norm_five {E : Type*} [SeminormedAddCommGroup E] (u v w x y : E) :
    ‖u + v - w + x + y‖ ≤ ‖u‖ + ‖v‖ + ‖w‖ + ‖x‖ + ‖y‖ := by
  have h1 := norm_add_le (u + v - w + x) y
  have h2 := norm_add_le (u + v - w) x
  have h3 := norm_sub_le (u + v) w
  have h4 := norm_add_le u v
  linarith

end FiniteContour

open FiniteContour in
theorem finiteLaplaceSum_vertical_bound_of_sector_resolvent
    {a M : ℝ} (ha : 0 < a) (hM : 0 ≤ M) :
    ∃ T B : ℝ, 0 < T ∧ 0 ≤ B ∧
      ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
        [CompleteSpace E] (ι : Type*) [Fintype ι]
        (lam : ι → ℝ) (v : ι → E),
        (∀ i, 0 ≤ lam i) →
        (∀ z : ℂ, z ≠ 0 → z.re ≤ a * |z.im| →
          ‖∑ i, (z - (lam i : ℂ))⁻¹ • v i‖ ≤ M / ‖z‖) →
        ∀ tau : ℝ, |tau| ≤ Real.pi →
          ‖∑ i, Complex.exp (-(((T : ℂ) + (tau : ℂ) * Complex.I) *
            (lam i : ℂ))) • v i‖ ≤ B := by
  classical
  obtain ⟨theta, htheta, htheta', hc, hslope⟩ := angle_exists ha
  let T := (Real.pi + 1) / Real.cos theta
  have hT : 0 < T := by dsimp [T]; positivity
  have hTc : T * Real.cos theta = Real.pi + 1 := div_mul_cancel₀ _ hc.ne'
  let B := (2 * Real.pi * (M * Real.exp (T + Real.pi)) + 2 * M + 1) / (2 * Real.pi)
  refine ⟨T, B, hT, by dsimp [B]; positivity, ?_⟩
  intro E _ _ _ ι _ lam v hl0 hr tau htau
  let w : ℂ := (T : ℂ) + (tau : ℂ) * I
  let S := ∑ i, ‖(lam i : ℂ)‖
  let V := ∑ i, ‖v i‖
  have hS : 0 ≤ S := Finset.sum_nonneg (fun i _ => norm_nonneg _)
  have hV : 0 ≤ V := Finset.sum_nonneg (fun i _ => norm_nonneg _)
  let b := 1 + 2 * S + 8 * Real.pi * V
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hexp := Real.add_one_le_exp b
  have hspec (i : ι) : ‖(lam i : ℂ)‖ ≤ Real.exp b / 2 := by
    have hi : ‖(lam i : ℂ)‖ ≤ S :=
      Finset.single_le_sum (fun j _ => norm_nonneg (lam j : ℂ)) (Finset.mem_univ i)
    dsimp [b] at hexp
    nlinarith [Real.pi_pos]
  have hspec' (i : ι) : ‖(lam i : ℂ)‖ < Real.exp b :=
    lt_of_le_of_lt (hspec i) (by linarith [Real.exp_pos b])
  let k := logKernel lam v w
  let D := (2 * V) * Real.exp (-Real.exp b)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have htail : 2 * (D * (2 * Real.pi)) ≤ 1 := by
    dsimp [D]
    rw [Real.exp_neg]
    have he2 := Real.add_one_le_exp (Real.exp b)
    have hnum : 8 * Real.pi * V ≤ Real.exp (Real.exp b) := by
      dsimp [b] at hexp
      linarith
    have hh := (div_le_one (Real.exp_pos (Real.exp b))).mpr hnum
    rw [div_eq_mul_inv] at hh
    nlinarith
  have horder : theta ≤ 2 * Real.pi - theta := by linarith [Real.pi_pos]
  have harc : ‖∫ y : ℝ in theta..2 * Real.pi - theta, k (y * I)‖ ≤
      2 * Real.pi * (M * Real.exp (T + Real.pi)) := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := theta) (b := 2 * Real.pi - theta) (f := fun y : ℝ => k (y * I)) (C := M * Real.exp (T + Real.pi))
      (by
        intro y hy
        rw [Set.uIoc_of_le horder] at hy
        exact logKernel_fixed_arc_bound lam v hM hT.le htau hr
          (left_arc_sector ha.le htheta.le htheta'.le hslope hy.1.le hy.2))
    rw [abs_of_nonneg (by linarith : 0 ≤ 2 * Real.pi - theta - theta)] at hh
    have hnn : 0 ≤ M * Real.exp (T + Real.pi) := by positivity
    nlinarith
  have hray1 : ‖∫ x : ℝ in 0..b, k (x + theta * I)‖ ≤ M :=
    ray_integral_bound hM hb (logKernel_ray_bound lam v hM hc hTc htau hr
      (hslope.trans (mul_le_mul_of_nonneg_left (le_abs_self _) ha.le)) rfl)
  have hray2 : ‖∫ x : ℝ in 0..b, k (x + ((2 * Real.pi - theta : ℝ) : ℂ) * I)‖ ≤ M := by
    apply ray_integral_bound hM hb
    apply logKernel_ray_bound lam v hM hc hTc htau hr
    · simpa only [Real.cos_two_pi_sub, Real.sin_two_pi_sub, abs_neg] using
        hslope.trans (mul_le_mul_of_nonneg_left (le_abs_self _) ha.le)
    · exact Real.cos_two_pi_sub theta
  have hout (p q : ℝ) (hpq : p ≤ q) (hlen : q - p ≤ 2 * Real.pi)
      (hy : ∀ y ∈ Set.Ioc p q, Real.cos theta ≤ Real.cos y) :
      ‖∫ y : ℝ in p..q, k (b + y * I)‖ ≤ D * (2 * Real.pi) := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := p) (b := q) (f := fun y : ℝ => k (b + y * I)) (C := D)
      (by
        intro y hyy
        rw [Set.uIoc_of_le hpq] at hyy
        exact logKernel_outer_bound lam v hc hTc htau hspec (hy y hyy))
    rw [abs_of_nonneg (sub_nonneg.mpr hpq)] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left hlen hD)
  have ho1 : ‖∫ y : ℝ in 0..theta, k (b + y * I)‖ ≤ D * (2 * Real.pi) := by
    apply hout 0 theta htheta.le (by linarith [Real.pi_pos])
    intro y hy
    exact Real.cos_le_cos_of_nonneg_of_le_pi hy.1.le
      (by linarith [Real.pi_pos]) hy.2
  have ho2 : ‖∫ y : ℝ in 2 * Real.pi - theta..2 * Real.pi, k (b + y * I)‖ ≤
      D * (2 * Real.pi) := by
    apply hout _ _ (by linarith) (by linarith [Real.pi_pos])
    intro y hy
    have hh := Real.cos_le_cos_of_nonneg_of_le_pi
      (by linarith [hy.2] : 0 ≤ 2 * Real.pi - y)
      (by linarith [Real.pi_pos] : theta ≤ Real.pi)
      (by linarith [hy.1] : 2 * Real.pi - y ≤ theta)
    simpa only [Real.cos_two_pi_sub] using hh
  have heq := finite_truncated_contour lam v w ha.le htheta.le htheta'.le hslope hl0 hspec'
  change (2 * Real.pi * I : ℂ) • laplace lam v w = _ at heq
  have hn := norm_five
    (I • (∫ y : ℝ in 0..theta, k (b + y * I)))
    (I • (∫ y : ℝ in theta..2 * Real.pi - theta, k (y * I)))
    (∫ x : ℝ in 0..b, k (x + theta * I))
    (∫ x : ℝ in 0..b, k (x + ((2 * Real.pi - theta : ℝ) : ℂ) * I))
    (I • (∫ y : ℝ in 2 * Real.pi - theta..2 * Real.pi, k (b + y * I)))
  rw [← heq] at hn
  simp only [norm_smul, norm_mul, norm_ofNat, norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos, norm_I, mul_one, one_mul] at hn
  change ‖laplace lam v w‖ ≤ B
  dsimp [B]
  apply (le_div_iff₀ Real.two_pi_pos).mpr
  nlinarith

end OAI

-- ---- platform node ----
open OAI
open Complex Set MeasureTheory Filter
open scoped BigOperators Interval Topology


theorem solution : type_of% @_root_.OAI.finiteLaplaceSum_vertical_bound_of_sector_resolvent := @_root_.OAI.finiteLaplaceSum_vertical_bound_of_sector_resolvent
