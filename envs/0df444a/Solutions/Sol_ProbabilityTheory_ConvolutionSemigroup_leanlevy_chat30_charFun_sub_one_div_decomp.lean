-- Prove2me | solution 1 for ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat30_charFun_sub_one_div_decomp
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T21:53:42.558395+00:00
-- url     : https://prove2.me/submissions/92483398-35a0-4d62-8106-1d99cb4dedd7

import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Complex Filter Topology
open ProbabilityTheory.ConvolutionSemigroup
open scoped NNReal ENNReal ComplexOrder
namespace ProbabilityTheory.ConvolutionSemigroup
private lemma integrable_charFun_integrand {μ : Measure ℝ} [IsFiniteMeasure μ] (ξ : ℝ) :
    Integrable (fun x : ℝ => exp ((↑(ξ * x) : ℂ) * I)) μ :=
  Integrable.of_bound
    ((Complex.continuous_ofReal.comp (continuous_const.mul continuous_id')).mul_const I
      |>.cexp.aestronglyMeasurable)
    1 (ae_of_all _ fun _ => le_of_eq (Complex.norm_exp_ofReal_mul_I _))
end ProbabilityTheory.ConvolutionSemigroup
theorem solution (S : ProbabilityTheory.ConvolutionSemigroup) (t : {t : ℝ // 0 < t}) (ξ : ℝ)
    {r : ℝ} (hr1 : r ≤ 1) :
    (charFun (S.measure t : Measure ℝ) ξ - 1) / (↑t.val : ℂ) =
      (↑t.val⁻¹ : ℂ) *
          ∫ x in {x | |x| < r}, ((↑x : ℂ) * ↑ξ * I) ∂(S.measure t : Measure ℝ)
      + (↑t.val⁻¹ : ℂ) *
          ∫ x in {x | |x| < r}, (exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I)
            ∂(S.measure t : Measure ℝ)
      + (↑t.val⁻¹ : ℂ) *
          ∫ x in largeSet r, (exp ((↑x : ℂ) * ↑ξ * I) - 1)
            ∂(S.measure t : Measure ℝ) := by
  set μ : Measure ℝ := (S.measure t : Measure ℝ) with hμ_def
  have hmeas_ball : MeasurableSet {x : ℝ | |x| < r} :=
    measurableSet_lt continuous_abs.measurable measurable_const
  have hball_compl : {x : ℝ | |x| < r} = (largeSet r)ᶜ := by
    ext x; simp only [largeSet, Set.mem_setOf_eq, Set.mem_compl_iff, not_le]
  -- Integrability of x ↦ exp(↑x*↑ξ*I) against μ.
  have hexp_int : Integrable (fun x : ℝ => exp ((↑x : ℂ) * ↑ξ * I)) μ := by
    refine (integrable_charFun_integrand (μ := μ) ξ).congr ?_
    refine Filter.Eventually.of_forall (fun x => ?_)
    push_cast; ring_nf
  -- Integrability of x ↦ exp(↑x*↑ξ*I) − 1.
  have hsub_int : Integrable (fun x : ℝ => exp ((↑x : ℂ) * ↑ξ * I) - 1) μ :=
    hexp_int.sub (integrable_const _)
  -- Integrability of x ↦ ↑x*↑ξ*I on {|x|<r} (bounded by |ξ|).
  have hxi_int : IntegrableOn (fun x : ℝ => (↑x : ℂ) * ↑ξ * I) {x | |x| < r} μ := by
    refine (integrable_const (|ξ|)).mono' ?_ ?_
    · exact ((Complex.measurable_ofReal.mul measurable_const).mul
        measurable_const).aestronglyMeasurable
    · refine (ae_restrict_iff' hmeas_ball).mpr ?_
      filter_upwards with x hx
      have hnorm : ‖((↑x : ℂ) * ↑ξ * I)‖ = |x| * |ξ| := by
        rw [show ((↑x : ℂ) * ↑ξ * I) = ((↑(x * ξ) : ℂ)) * I from by
              push_cast; ring,
            norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
            Real.norm_eq_abs, abs_mul]
      rw [hnorm]
      calc |x| * |ξ| ≤ 1 * |ξ| :=
            mul_le_mul_of_nonneg_right (le_of_lt (lt_of_lt_of_le hx hr1)) (abs_nonneg _)
        _ = |ξ| := one_mul _
  -- Integrability of the compensated remainder on {|x|<r}.
  have hrem_int : IntegrableOn
      (fun x : ℝ => exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I) {x | |x| < r} μ :=
    (hsub_int.integrableOn).sub hxi_int
  -- Step 1: (charFun μ ξ − 1) = ∫ (exp(ixξ) − 1) dμ.
  have h_one : (∫ _ : ℝ, (1 : ℂ) ∂μ) = 1 := by simp
  have h1 : charFun μ ξ - 1 = ∫ x, (exp ((↑x : ℂ) * ↑ξ * I) - 1) ∂μ := by
    have hcf : charFun μ ξ = ∫ x, exp ((↑x : ℂ) * ↑ξ * I) ∂μ := by
      rw [charFun_apply_real]; congr 1; ext x; congr 1; ring
    calc charFun μ ξ - 1
        = (∫ x, exp ((↑x : ℂ) * ↑ξ * I) ∂μ) - ∫ _ : ℝ, (1 : ℂ) ∂μ := by
            rw [hcf, h_one]
      _ = ∫ x, (exp ((↑x : ℂ) * ↑ξ * I) - 1) ∂μ :=
          (integral_sub hexp_int (integrable_const 1)).symm
  -- Step 2: split via {|x|<r}/largeSet r.
  have hcompl_ball : ({x : ℝ | |x| < r})ᶜ = largeSet r := by
    rw [hball_compl, compl_compl]
  have h2 : ∫ x, (exp ((↑x : ℂ) * ↑ξ * I) - 1) ∂μ
      = ∫ x in {x | |x| < r}, (exp ((↑x : ℂ) * ↑ξ * I) - 1) ∂μ
        + ∫ x in largeSet r, (exp ((↑x : ℂ) * ↑ξ * I) - 1) ∂μ := by
    have hs := (integral_add_compl hmeas_ball hsub_int).symm
    rw [hcompl_ball] at hs
    exact hs
  -- Step 3: split the {|x|<r} integral additively.
  have h3 : ∫ x in {x | |x| < r}, (exp ((↑x : ℂ) * ↑ξ * I) - 1) ∂μ
      = ∫ x in {x | |x| < r}, ((↑x : ℂ) * ↑ξ * I) ∂μ
        + ∫ x in {x | |x| < r}, (exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I) ∂μ := by
    rw [← integral_add hxi_int hrem_int]
    refine setIntegral_congr_fun hmeas_ball (fun x _ => ?_)
    ring
  rw [h1, h2, h3]
  push_cast
  ring
