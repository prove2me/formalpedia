-- Prove2me | solution 1 for ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat33_scaled_largeSet_charFun_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T11:25:10.684199+00:00
-- url     : https://prove2.me/submissions/af740deb-f311-4726-92ed-4a225d585872

import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Theorems.Thm_ProbabilityTheory_ConvolutionSemigroup_leanlevy_chat32_scaled_largeSet_integral_tendsto
import Theorems.Thm_levy_foundations_public_largeSet_charFun_real_im_integral

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

/-- A bounded continuous function is integrable over a finite-mass set. -/
private lemma levy_foundations_aux_integrableOn_bounded {s : Set ℝ} {μ : Measure ℝ}
    (hs : μ s < ⊤) {E : Type*} [NormedAddCommGroup E]
    {f : ℝ → E} (hf_cont : Continuous f) {M : ℝ}
    (hf_bnd : ∀ x, ‖f x‖ ≤ M) :
    IntegrableOn f s μ := by
  haveI : IsFiniteMeasure (μ.restrict s) := isFiniteMeasure_restrict.mpr hs.ne
  exact Integrable.mono' (integrable_const M) hf_cont.aestronglyMeasurable
    (Filter.Eventually.of_forall hf_bnd)

/-- Complex large-jump convergence by scalar real/imaginary-part convergence. -/
theorem solution (S : ProbabilityTheory.ConvolutionSemigroup)
    {ρ : ℝ} (hρ : 0 < ρ) (ξ : ℝ)
    {ν : Measure ℝ} (hν : IsLevyMeasure ν) (hν_atom : ν {x | |x| = ρ} = 0)
    {t_seq : ℕ → {t : ℝ // 0 < t}}
    (h_jump : ∀ (f : BoundedContinuousFunction ℝ ℝ),
        (∃ r > 0, ∀ x, |x| < r → f x = 0) →
        Tendsto (fun k => (t_seq k).val⁻¹ * ∫ x, f x ∂(S.measure (t_seq k) : Measure ℝ))
          atTop (𝓝 (∫ x, f x ∂ν))) :
    Tendsto (fun k => ((t_seq k).val⁻¹ : ℂ) *
        ∫ x in largeSet ρ, (exp ((↑x : ℂ) * ↑ξ * I) - 1) ∂(S.measure (t_seq k) : Measure ℝ))
      atTop (𝓝 (∫ x in largeSet ρ, (exp ((↑x : ℂ) * ↑ξ * I) - 1) ∂ν)) := by
  -- Real and imaginary parts of the complex integrand.
  set gRe : ℝ → ℝ := fun x => Real.cos (x * ξ) - 1 with hgRe_def
  set gIm : ℝ → ℝ := fun x => Real.sin (x * ξ) with hgIm_def
  -- Continuity.
  have hgRe_cont : Continuous gRe :=
    (Real.continuous_cos.comp (continuous_id.mul continuous_const)).sub continuous_const
  have hgIm_cont : Continuous gIm :=
    Real.continuous_sin.comp (continuous_id.mul continuous_const)
  -- Bounds: |gRe| ≤ 2, |gIm| ≤ 1.
  have hgRe_bnd : ∀ x, |gRe x| ≤ 2 := fun x =>
    abs_le.mpr ⟨by simp only [hgRe_def]; linarith [Real.neg_one_le_cos (x * ξ)],
                by simp only [hgRe_def]; linarith [Real.cos_le_one (x * ξ)]⟩
  have hgIm_bnd : ∀ x, |gIm x| ≤ 1 := fun x =>
    abs_le.mpr ⟨Real.neg_one_le_sin (x * ξ), Real.sin_le_one (x * ξ)⟩
  -- The public real/imaginary decomposition isolates the finite-mass analysis.
  have hExp_arg : ∀ x : ℝ, (↑x : ℂ) * ↑ξ * I = (↑(x * ξ) : ℂ) * I := fun x => by
    push_cast
    ring
  have h_decomp : ∀ (m : Measure ℝ), m (largeSet ρ) < ⊤ →
      ∫ x in largeSet ρ, (exp ((↑x : ℂ) * ↑ξ * I) - 1) ∂m =
        (↑(∫ x in largeSet ρ, gRe x ∂m) : ℂ)
        + (↑(∫ x in largeSet ρ, gIm x ∂m) : ℂ) * I := by
    intro m hm
    have h_int : IntegrableOn
        (fun x : ℝ => exp ((↑x : ℂ) * ↑ξ * I) - 1) (largeSet ρ) m := by
      refine levy_foundations_aux_integrableOn_bounded hm
        (((Complex.continuous_exp.comp
          (((Complex.continuous_ofReal.mul continuous_const).mul continuous_const))).sub
          continuous_const)) (M := 2) (fun x => ?_)
      rw [show exp ((↑x : ℂ) * ↑ξ * I) - 1 =
          exp ((↑(x * ξ) : ℂ) * I) - 1 from by rw [hExp_arg]]
      calc ‖exp ((↑(x * ξ) : ℂ) * I) - 1‖
          ≤ ‖exp ((↑(x * ξ) : ℂ) * I)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 2 := by
            rw [Complex.norm_exp_ofReal_mul_I, norm_one]
            norm_num
    simpa only [hgRe_def, hgIm_def] using
      (levy_foundations_public_largeSet_charFun_real_im_integral m ρ ξ h_int)
  -- Scalar limits for gRe and gIm.
  have h_re_lim : Tendsto (fun k => (t_seq k).val⁻¹ *
      ∫ x in largeSet ρ, gRe x ∂(S.measure (t_seq k) : Measure ℝ))
      atTop (𝓝 (∫ x in largeSet ρ, gRe x ∂ν)) :=
    S.leanlevy_chat32_scaled_largeSet_integral_tendsto hρ gRe hgRe_cont (by norm_num) hgRe_bnd hν hν_atom h_jump
  have h_im_lim : Tendsto (fun k => (t_seq k).val⁻¹ *
      ∫ x in largeSet ρ, gIm x ∂(S.measure (t_seq k) : Measure ℝ))
      atTop (𝓝 (∫ x in largeSet ρ, gIm x ∂ν)) :=
    S.leanlevy_chat32_scaled_largeSet_integral_tendsto hρ gIm hgIm_cont (by norm_num) hgIm_bnd hν hν_atom h_jump
  -- Recombine into the complex limit.
  have h_re_lim_C : Tendsto (fun k => (↑((t_seq k).val⁻¹ *
      ∫ x in largeSet ρ, gRe x ∂(S.measure (t_seq k) : Measure ℝ)) : ℂ))
      atTop (𝓝 (↑(∫ x in largeSet ρ, gRe x ∂ν) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp h_re_lim
  have h_im_lim_C : Tendsto (fun k => (↑((t_seq k).val⁻¹ *
      ∫ x in largeSet ρ, gIm x ∂(S.measure (t_seq k) : Measure ℝ)) : ℂ) * I)
      atTop (𝓝 ((↑(∫ x in largeSet ρ, gIm x ∂ν) : ℂ) * I)) :=
    ((Complex.continuous_ofReal.tendsto _).comp h_im_lim).mul_const I
  have h_sum := h_re_lim_C.add h_im_lim_C
  rw [← h_decomp ν (hν.measure_setOf_abs_ge_lt_top hρ)] at h_sum
  refine h_sum.congr (fun k => ?_)
  rw [h_decomp (S.measure (t_seq k) : Measure ℝ) (measure_lt_top _ _)]
  push_cast
  ring

