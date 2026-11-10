-- Prove2me | solution 1 for ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat32_remainder_band_tendsto
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T00:17:53.582507+00:00
-- url     : https://prove2.me/submissions/3a25a426-c8d3-4ed3-9731-882e7b520f93
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Theorems.Thm_ProbabilityTheory_leanlevy_chat32_remainder_clamp_continuous
import Theorems.Thm_ProbabilityTheory_leanlevy_chat32_remainder_clamp_norm_le
import Theorems.Thm_ProbabilityTheory_leanlevy_chat32_clamp_eq_of_abs_lt
import Theorems.Thm_ProbabilityTheory_leanlevy_chat32_integrableOn_of_bounded_of_measure_lt_top
import Theorems.Thm_ProbabilityTheory_ConvolutionSemigroup_leanlevy_chat32_scaled_band_integral_tendsto
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.Positivity
import Mathlib.Topology.ContinuousMap.Bounded.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

theorem solution (S : ConvolutionSemigroup)
    {δ r : ℝ} (hδ : 0 < δ) (hδr : δ < r) (hr1 : r ≤ 1) (ξ : ℝ)
    {ν : Measure ℝ} (hν : IsLevyMeasure ν)
    (hν_δ : ν {x | |x| = δ} = 0) (hν_r : ν {x | |x| = r} = 0)
    {t_seq : ℕ → {t : ℝ // 0 < t}}
    (h_jump : ∀ (f : BoundedContinuousFunction ℝ ℝ),
        (∃ r > 0, ∀ x, |x| < r → f x = 0) →
        Tendsto (fun k => (t_seq k).val⁻¹ * ∫ x, f x ∂(S.measure (t_seq k) : Measure ℝ))
          atTop (𝓝 (∫ x, f x ∂ν))) :
    Tendsto (fun k => ((t_seq k).val⁻¹ : ℂ) *
        ∫ x in {x | δ ≤ |x| ∧ |x| < r},
          (exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I + ((↑x : ℂ) * ↑ξ) ^ 2 / 2)
          ∂(S.measure (t_seq k) : Measure ℝ))
      atTop (𝓝 (∫ x in {x | δ ≤ |x| ∧ |x| < r},
          (exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I + ((↑x : ℂ) * ↑ξ) ^ 2 / 2) ∂ν)) := by
  have hr0 : (0 : ℝ) ≤ r := le_of_lt (hδ.trans hδr)
  set R : ℝ → ℂ := fun x =>
    exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I + ((↑x : ℂ) * ↑ξ) ^ 2 / 2 with hR_def
  -- Clamped real and imaginary parts, globally bounded by `M := 2 + |ξ| + ξ²/2`.
  set M : ℝ := 2 + |ξ| + ξ ^ 2 / 2 with hM_def
  have hM_nn : (0 : ℝ) ≤ M := by positivity
  set Rc : ℝ → ℂ := fun x => R (max (-r) (min x r)) with hRc_def
  have hRc_cont : Continuous Rc := ProbabilityTheory.leanlevy_chat32_remainder_clamp_continuous r ξ
  have hRc_bnd : ∀ x, ‖Rc x‖ ≤ M := ProbabilityTheory.leanlevy_chat32_remainder_clamp_norm_le hr0 hr1 ξ
  set gRe : ℝ → ℝ := fun x => (Rc x).re with hgRe_def
  set gIm : ℝ → ℝ := fun x => (Rc x).im with hgIm_def
  have hgRe_cont : Continuous gRe := Complex.continuous_re.comp hRc_cont
  have hgIm_cont : Continuous gIm := Complex.continuous_im.comp hRc_cont
  have hgRe_bnd : ∀ x, |gRe x| ≤ M := fun x =>
    (abs_re_le_norm (Rc x)).trans (hRc_bnd x)
  have hgIm_bnd : ∀ x, |gIm x| ≤ M := fun x =>
    (abs_im_le_norm (Rc x)).trans (hRc_bnd x)
  -- The band, measurable and contained in the ball.
  set band : Set ℝ := {x | δ ≤ |x| ∧ |x| < r} with hband_def
  have h_meas_band : MeasurableSet band :=
    (measurableSet_le measurable_const continuous_abs.measurable).inter
      (measurableSet_lt continuous_abs.measurable measurable_const)
  -- On the band, `Rc = R` (the clamp is inactive since `|x| < r`).
  have hRc_eq : ∀ x ∈ band, Rc x = R x := fun x hx => by
    show R (max (-r) (min x r)) = R x
    rw [ProbabilityTheory.leanlevy_chat32_clamp_eq_of_abs_lt hx.2]
  -- The band has finite `ν`-mass (it avoids a neighbourhood of `0`).
  have hν_band : ν band < ⊤ :=
    lt_of_le_of_lt (measure_mono (fun x hx => hx.1)) (hν.measure_setOf_abs_ge_lt_top hδ)
  -- Decomposition of the complex band integral via Re/Im of `Rc`, for any measure finite on the band.
  have h_decomp : ∀ (m : Measure ℝ), m band < ⊤ →
      ∫ x in band, R x ∂m =
        (↑(∫ x in band, gRe x ∂m) : ℂ) + (↑(∫ x in band, gIm x ∂m) : ℂ) * I := by
    intro m hm
    have hR_int : IntegrableOn R band m := by
      have : IntegrableOn Rc band m :=
        ProbabilityTheory.leanlevy_chat32_integrableOn_of_bounded_of_measure_lt_top hm hRc_cont (fun x => by
          simpa [Real.norm_eq_abs] using hRc_bnd x)
      exact this.congr_fun hRc_eq h_meas_band
    have h := setIntegral_re_add_im hR_int
    simp only [RCLike.I_to_complex] at h
    have hRe_int : ∫ x in band, RCLike.re (R x) ∂m = ∫ x in band, gRe x ∂m :=
      setIntegral_congr_fun h_meas_band (fun x hx => by
        simp only [hgRe_def, RCLike.re_to_complex, hRc_eq x hx])
    have hIm_int : ∫ x in band, RCLike.im (R x) ∂m = ∫ x in band, gIm x ∂m :=
      setIntegral_congr_fun h_meas_band (fun x hx => by
        simp only [hgIm_def, RCLike.im_to_complex, hRc_eq x hx])
    rw [hRe_int, hIm_int] at h
    exact h.symm
  -- Scalar band limits for `gRe`, `gIm`.
  have h_re_lim : Tendsto (fun k => (t_seq k).val⁻¹ *
      ∫ x in band, gRe x ∂(S.measure (t_seq k) : Measure ℝ))
      atTop (𝓝 (∫ x in band, gRe x ∂ν)) :=
    ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat32_scaled_band_integral_tendsto S hδ hδr gRe hgRe_cont hM_nn hgRe_bnd
      hν hν_δ hν_r h_jump
  have h_im_lim : Tendsto (fun k => (t_seq k).val⁻¹ *
      ∫ x in band, gIm x ∂(S.measure (t_seq k) : Measure ℝ))
      atTop (𝓝 (∫ x in band, gIm x ∂ν)) :=
    ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat32_scaled_band_integral_tendsto S hδ hδr gIm hgIm_cont hM_nn hgIm_bnd
      hν hν_δ hν_r h_jump
  -- Recombine into the complex limit.
  have h_re_lim_C : Tendsto (fun k => (↑((t_seq k).val⁻¹ *
      ∫ x in band, gRe x ∂(S.measure (t_seq k) : Measure ℝ)) : ℂ))
      atTop (𝓝 (↑(∫ x in band, gRe x ∂ν) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp h_re_lim
  have h_im_lim_C : Tendsto (fun k => (↑((t_seq k).val⁻¹ *
      ∫ x in band, gIm x ∂(S.measure (t_seq k) : Measure ℝ)) : ℂ) * I)
      atTop (𝓝 ((↑(∫ x in band, gIm x ∂ν) : ℂ) * I)) :=
    ((Complex.continuous_ofReal.tendsto _).comp h_im_lim).mul_const I
  have h_sum := h_re_lim_C.add h_im_lim_C
  rw [← h_decomp ν hν_band] at h_sum
  refine h_sum.congr (fun k => ?_)
  rw [h_decomp (S.measure (t_seq k) : Measure ℝ) (measure_lt_top _ _)]
  push_cast
  ring
