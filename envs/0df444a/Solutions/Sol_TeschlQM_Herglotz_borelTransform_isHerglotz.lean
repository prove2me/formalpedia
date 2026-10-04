-- Prove2me | solution 1 for TeschlQM.Herglotz.borelTransform_isHerglotz
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-03T19:02:02.279566+00:00
-- url     : https://prove2.me/submissions/bf76b631-d948-410f-9fd1-731ed6abb9b1

import Mathlib
import Definitions.Def_TeschlQM_Herglotz_IsHerglotz
import Definitions.Def_TeschlQM_Herglotz_borelTransform
import Definitions.Def_TeschlQM_Herglotz_measureSpectrum

open MeasureTheory Filter Topology

namespace TeschlQM.Herglotz

/-- Near a point `z₀` off the spectrum, `‖t - z‖` is bounded below for `μ`-a.e. `t`, uniformly
for `z` in a ball around `z₀`. -/
lemma exists_ball_bound_core (μ : Measure ℝ) (z₀ : ℂ)
    (hz₀ : ∀ t ∈ measureSpectrum μ, z₀ ≠ (t : ℂ)) :
    ∃ r > 0, ∃ δ > 0, ∀ᵐ (t : ℝ) ∂μ, ∀ z ∈ Metric.ball z₀ r, δ ≤ ‖(t : ℂ) - z‖ := by
  by_cases him : z₀.im = 0
  · -- `z₀` is a real point outside the spectrum
    have hx : z₀.re ∉ measureSpectrum μ := by
      intro h
      apply hz₀ z₀.re h
      apply Complex.ext <;> simp [him]
    simp only [measureSpectrum, Set.mem_setOf_eq, not_forall, not_lt, nonpos_iff_eq_zero] at hx
    obtain ⟨ε, hε, hμ⟩ := hx
    refine ⟨ε / 2, by positivity, ε / 2, by positivity, ?_⟩
    have hae : ∀ᵐ (t : ℝ) ∂μ, t ∉ Set.Ioo (z₀.re - ε) (z₀.re + ε) :=
      ae_iff.mpr (by simp only [not_not, Set.setOf_mem_eq]; exact hμ)
    filter_upwards [hae] with t ht z hz
    have h1 : ε ≤ |t - z₀.re| := by
      simp only [Set.mem_Ioo, not_and_or, not_lt] at ht
      rcases ht with h | h
      · rw [abs_of_nonpos (by linarith)]; linarith
      · rw [abs_of_nonneg (by linarith)]; linarith
    have h2 : ‖(t : ℂ) - z₀‖ = |t - z₀.re| := by
      have : z₀ = (z₀.re : ℂ) := by apply Complex.ext <;> simp [him]
      rw [this, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_re]
    have h3 : ‖z - z₀‖ < ε / 2 := mem_ball_iff_norm.mp hz
    calc ε / 2 = ε - ε / 2 := by ring
      _ ≤ ‖(t : ℂ) - z₀‖ - ‖z - z₀‖ := by rw [h2]; linarith
      _ ≤ ‖(t : ℂ) - z‖ := by
        have := norm_add_le ((t : ℂ) - z) (z - z₀)
        rw [sub_add_sub_cancel] at this
        linarith
  · -- `z₀` is not real
    refine ⟨|z₀.im| / 2, by positivity, |z₀.im| / 2, by positivity, ?_⟩
    refine Eventually.of_forall fun (t : ℝ) z hz => ?_
    have h3 : ‖z - z₀‖ < |z₀.im| / 2 := mem_ball_iff_norm.mp hz
    have h4 : |z.im - z₀.im| ≤ ‖z - z₀‖ := by
      rw [← Complex.sub_im]; exact Complex.abs_im_le_norm _
    have h5 : |z.im| ≥ |z₀.im| / 2 := by
      have := abs_sub_abs_le_abs_sub z₀.im z.im
      rw [abs_sub_comm] at this
      linarith
    calc |z₀.im| / 2 ≤ |z.im| := h5
      _ = |((t : ℂ) - z).im| := by simp
      _ ≤ ‖(t : ℂ) - z‖ := Complex.abs_im_le_norm _

/-- The Borel transform is complex differentiable at every point off the spectrum. -/
lemma differentiableAt_core (μ : Measure ℝ) [IsFiniteMeasure μ] (z₀ : ℂ)
    (hz₀ : ∀ t ∈ measureSpectrum μ, z₀ ≠ (t : ℂ)) :
    DifferentiableAt ℂ (borelTransform μ) z₀ := by
  obtain ⟨r, hr, δ, hδ, hae⟩ := exists_ball_bound_core μ z₀ hz₀
  let F : ℂ → ℝ → ℂ := fun z t => ((t : ℂ) - z)⁻¹
  let F' : ℂ → ℝ → ℂ := fun z t => -(-1) / ((t : ℂ) - z) ^ 2
  have hmeas : ∀ z : ℂ, AEStronglyMeasurable (F z) μ := fun z =>
    ((Complex.measurable_ofReal.sub_const z).inv).aestronglyMeasurable
  have hmeas' : AEStronglyMeasurable (F' z₀) μ :=
    (measurable_const.div ((Complex.measurable_ofReal.sub_const z₀).pow_const 2)).aestronglyMeasurable
  have hz₀r : z₀ ∈ Metric.ball z₀ r := Metric.mem_ball_self hr
  have hint : Integrable (F z₀) μ := by
    refine Integrable.of_bound (hmeas z₀) δ⁻¹ ?_
    filter_upwards [hae] with t ht
    have h := ht z₀ hz₀r
    simp only [F, norm_inv]
    exact inv_anti₀ hδ h
  have hbound : ∀ᵐ t ∂μ, ∀ z ∈ Metric.ball z₀ r, ‖F' z t‖ ≤ δ⁻¹ ^ 2 := by
    filter_upwards [hae] with t ht z hz
    have h := ht z hz
    simp only [F', neg_neg, one_div, norm_inv, norm_pow, inv_pow]
    exact inv_anti₀ (pow_pos hδ 2) (pow_le_pow_left₀ hδ.le h 2)
  have hdiff : ∀ᵐ t ∂μ, ∀ z ∈ Metric.ball z₀ r, HasDerivAt (fun w => F w t) (F' z t) z := by
    filter_upwards [hae] with t ht z hz
    have h := ht z hz
    have hne : (t : ℂ) - z ≠ 0 := by
      intro h0; rw [h0, norm_zero] at h; linarith
    have hc : HasDerivAt (fun w : ℂ => (t : ℂ) - w) (-1) z := by
      simpa using (hasDerivAt_id z).const_sub (t : ℂ)
    exact hc.inv hne
  have := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (F := F) (F' := F')
    (bound := fun _ => δ⁻¹ ^ 2) (Metric.isOpen_ball.mem_nhds hz₀r)
    (Eventually.of_forall hmeas) hint hmeas' hbound (integrable_const _) hdiff).2
  exact this.differentiableAt

end TeschlQM.Herglotz

open TeschlQM.Herglotz in
theorem solution (μ : Measure ℝ) [IsFiniteMeasure μ] :
    (μ ≠ 0 → IsHerglotz (borelTransform μ)) ∧
    DifferentiableOn ℂ (borelTransform μ) {z : ℂ | ∀ t ∈ measureSpectrum μ, z ≠ (t : ℂ)} ∧
    ∀ z : ℂ, 0 < z.im →
      borelTransform μ (starRingEnd ℂ z) = starRingEnd ℂ (borelTransform μ z) ∧
      ‖borelTransform μ z‖ ≤ (μ Set.univ).toReal / z.im := by
  have hdiff : DifferentiableOn ℂ (borelTransform μ)
      {z : ℂ | ∀ t ∈ measureSpectrum μ, z ≠ (t : ℂ)} :=
    fun z hz => (differentiableAt_core μ z hz).differentiableWithinAt
  -- a basic norm bound for `Im z > 0`
  have hnorm : ∀ z : ℂ, 0 < z.im → ∀ t : ℝ, ‖((t : ℂ) - z)⁻¹‖ ≤ (z.im)⁻¹ := by
    intro z hz t
    rw [norm_inv]
    apply inv_anti₀ hz
    calc z.im = |((t : ℂ) - z).im| := by simp [abs_of_pos hz]
      _ ≤ ‖(t : ℂ) - z‖ := Complex.abs_im_le_norm _
  have hint : ∀ z : ℂ, 0 < z.im → Integrable (fun t : ℝ => ((t : ℂ) - z)⁻¹) μ := fun z hz =>
    Integrable.of_bound ((Complex.measurable_ofReal.sub_const z).inv).aestronglyMeasurable _
      (Eventually.of_forall (hnorm z hz))
  refine ⟨fun hμ => ⟨hdiff.mono ?_, ?_⟩, hdiff, fun z hz => ⟨?_, ?_⟩⟩
  · intro z hz t _ h
    have hz' : 0 < z.im := hz
    have := congrArg Complex.im h
    simp at this
    linarith
  · intro z hz
    unfold borelTransform
    change 0 < RCLike.im (∫ t : ℝ, ((t : ℂ) - z)⁻¹ ∂μ)
    rw [← integral_im (hint z hz)]
    have hpos : ∀ t : ℝ, 0 < (((t : ℂ) - z)⁻¹).im := by
      intro t
      rw [Complex.inv_im]
      have hne : (t : ℂ) - z ≠ 0 := by
        intro h0; have := congrArg Complex.im h0; simp at this; linarith
      have : 0 < Complex.normSq ((t : ℂ) - z) := Complex.normSq_pos.mpr hne
      simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, neg_neg]
      positivity
    rw [integral_pos_iff_support_of_nonneg (f := fun t : ℝ => RCLike.im (((t : ℂ) - z)⁻¹))
      (fun t => (hpos t).le) ((hint z hz).im)]
    have hsupp : Function.support (fun t : ℝ => RCLike.im (((t : ℂ) - z)⁻¹)) = Set.univ :=
      Set.eq_univ_of_forall fun t => (hpos t).ne'
    rw [hsupp]
    exact Measure.measure_univ_pos.mpr hμ
  · unfold borelTransform
    rw [← integral_conj]
    congr 1
    funext t
    simp [map_inv₀, map_sub, Complex.conj_ofReal]
  · unfold borelTransform
    have := norm_integral_le_of_norm_le_const (μ := μ) (f := fun t : ℝ => ((t : ℂ) - z)⁻¹)
      (C := (z.im)⁻¹) (Eventually.of_forall (hnorm z hz))
    calc ‖∫ t : ℝ, ((t : ℂ) - z)⁻¹ ∂μ‖ ≤ (z.im)⁻¹ * μ.real Set.univ := this
      _ = (μ Set.univ).toReal / z.im := by rw [measureReal_def]; ring

#print axioms solution
