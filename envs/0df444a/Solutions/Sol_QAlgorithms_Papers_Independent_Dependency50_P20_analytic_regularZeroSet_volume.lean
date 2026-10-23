-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P20.analytic_regularZeroSet_volume
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T14:15:24.535724+00:00
-- url     : https://prove2.me/submissions/0e861753-23a0-4dd5-8c82-1b460938dbdb

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P20

open Set MeasureTheory Filter
open scoped Topology ContDiff NNReal

namespace X6P20

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]

/-- the auxiliary map straightening the level set -/
def phi (B : E → ℝ) (L : E →L[ℝ] ℝ) (v : E) (y : E) : E := y + (B y - L y) • v

/-- local nullity of the zero set near a regular zero -/
theorem local_null (U : Set E) (hU : IsOpen U) (B : E → ℝ) (hB : ContDiffOn ℝ 1 B U)
    (x0 : E) (hx0 : x0 ∈ U) (hL : fderiv ℝ B x0 ≠ 0) :
    ∃ r > 0, μ (Metric.closedBall x0 r ∩ B ⁻¹' {0}) = 0 := by
  set L := fderiv ℝ B x0 with hLdef
  obtain ⟨w, hw⟩ : ∃ w, L w ≠ 0 := by
    by_contra h; push Not at h; exact hL (ContinuousLinearMap.ext h)
  set v : E := (L w)⁻¹ • w with hv
  have hLv : L v = 1 := by simp [hv, hw]
  have hBd : ∀ y ∈ U, HasFDerivAt B (fderiv ℝ B y) y := fun y hy =>
    ((hB.contDiffAt (hU.mem_nhds hy)).differentiableAt (by norm_num)).hasFDerivAt
  have hcont : ContinuousOn (fun y => fderiv ℝ B y) U :=
    hB.continuousOn_fderiv_of_isOpen hU le_rfl
  -- strict derivative of phi at x0 is the identity
  have hstrict : HasStrictFDerivAt (phi B L v)
      ((ContinuousLinearEquiv.refl ℝ E : E ≃L[ℝ] E) : E →L[ℝ] E) x0 := by
    have h1 : HasStrictFDerivAt B L x0 :=
      (hB.contDiffAt (hU.mem_nhds hx0)).hasStrictFDerivAt (by norm_num)
    have h2 : HasStrictFDerivAt (fun y => B y - L y) (L - L) x0 := h1.sub L.hasStrictFDerivAt
    have h3 := HasStrictFDerivAt.add (h2.smul_const v) (hasStrictFDerivAt_id x0)
    convert h3 using 1
    · funext h; simp [phi, add_comm]
    · ext h; simp
  obtain ⟨t, ht, happrox⟩ := hstrict.approximates_deriv_on_nhds (c := (1/2 : ℝ≥0)) (Or.inr (by norm_num))
  -- neighbourhood where B' v > 1/2
  have hev : ∀ᶠ y in 𝓝 x0, y ∈ U ∧ 1/2 < fderiv ℝ B y v := by
    refine Filter.Eventually.and (hU.mem_nhds hx0) ?_
    have hc : ContinuousAt (fun y => fderiv ℝ B y v) x0 :=
      ((ContinuousLinearMap.apply ℝ ℝ v).continuous.continuousAt).comp
        (hcont.continuousAt (hU.mem_nhds hx0))
    have : (1/2 : ℝ) < fderiv ℝ B x0 v := by rw [← hLdef, hLv]; norm_num
    exact hc.eventually (lt_mem_nhds this)
  obtain ⟨r, hr, hrsub⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (inter_mem ht hev)
  refine ⟨r, hr, ?_⟩
  set s := Metric.closedBall x0 r ∩ B ⁻¹' {0} with hs
  have hsU : ∀ y ∈ s, y ∈ t ∧ y ∈ U ∧ 1/2 < fderiv ℝ B y v := fun y hy =>
    ⟨(hrsub hy.1).1, (hrsub hy.1).2.1, (hrsub hy.1).2.2⟩
  have hsmeas : MeasurableSet s := by
    have : IsClosed s := ContinuousOn.preimage_isClosed_of_isClosed
      (fun y hy => (hBd y (hrsub hy).2.1).continuousAt.continuousWithinAt)
      Metric.isClosed_closedBall isClosed_singleton
    exact this.measurableSet
  -- derivative of phi
  set D : E → E →L[ℝ] E := fun y =>
    ContinuousLinearMap.id ℝ E + (fderiv ℝ B y - L).smulRight v with hD
  have hderiv : ∀ y ∈ s, HasFDerivWithinAt (phi B L v) (D y) s y := by
    intro y hy
    have h2 : HasFDerivAt (fun y => B y - L y) (fderiv ℝ B y - L) y :=
      (hBd y (hsU y hy).2.1).sub L.hasFDerivAt
    have h3 := (h2.smul_const v).add (hasFDerivAt_id y)
    have : HasFDerivAt (phi B L v) (D y) y := by
      convert h3 using 1
      · ext z; simp [phi, add_comm]
      · ext h; simp [hD, add_comm]
    exact this.hasFDerivWithinAt
  have hinj : InjOn (phi B L v) s := by
    have := happrox.injOn (by
      by_cases hE : Subsingleton E
      · exact Or.inl hE
      · right
        rw [not_subsingleton_iff_nontrivial] at hE
        simp only [ContinuousLinearEquiv.refl_symm, ContinuousLinearEquiv.coe_refl,
          ContinuousLinearMap.nnnorm_id, inv_one]
        norm_num)
    exact this.mono fun y hy => (hsU y hy).1
  have himage : μ (phi B L v '' s) = 0 := by
    apply measure_mono_null _ (Measure.addHaar_submodule μ (LinearMap.ker (L : E →ₗ[ℝ] ℝ)) ?_)
    · rintro _ ⟨y, hy, rfl⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, phi, map_add,
        map_smul, hLv, smul_eq_mul, mul_one]
      have : B y = 0 := hy.2
      linarith
    · intro htop
      apply hw
      have : w ∈ LinearMap.ker (L : E →ₗ[ℝ] ℝ) := htop ▸ Submodule.mem_top
      simpa using this
  have hint := lintegral_abs_det_fderiv_le_addHaar_image μ hsmeas hderiv hinj
  rw [himage, nonpos_iff_eq_zero] at hint
  have hmeasf : AEMeasurable (fun y => ENNReal.ofReal |(D y).det|) (μ.restrict s) := by
    apply ContinuousOn.aemeasurable _ hsmeas
    apply ENNReal.continuous_ofReal.comp_continuousOn
    apply continuous_abs.comp_continuousOn
    apply ContinuousLinearMap.continuous_det.comp_continuousOn
    apply continuousOn_const.add
    have : ContinuousOn (fun y => fderiv ℝ B y - L) s :=
      (hcont.mono fun y hy => (hsU y hy).2.1).sub continuousOn_const
    exact ((ContinuousLinearMap.smulRightL ℝ E E).flip v).continuous.comp_continuousOn this
  rw [setLIntegral_eq_zero_iff' hsmeas hmeasf] at hint
  rw [measure_eq_zero_iff_ae_notMem]
  filter_upwards [hint] with y hy hys
  have hdet : (D y).det ≠ 0 := by
    intro h0
    have hk := LinearMap.det_eq_zero_iff_ker_ne_bot.1 h0
    apply hk
    rw [LinearMap.ker_eq_bot']
    intro h hh
    have hh' : h + (fderiv ℝ B y h - L h) • v = 0 := by simpa [hD] using hh
    have e1 := congrArg L hh'
    have e2 := congrArg (fderiv ℝ B y) hh'
    simp only [map_add, map_smul, hLv, smul_eq_mul, mul_one, map_zero] at e1 e2
    have hc := (hsU y hys).2.2
    have ha : fderiv ℝ B y h = 0 := by linarith
    have hb : L h = 0 := by
      rw [ha] at e2
      have : L h * fderiv ℝ B y v = 0 := by linarith
      rcases mul_eq_zero.1 this with h1 | h1
      · exact h1
      · linarith
    rw [ha, hb] at hh'
    simpa using hh'
  have := hy hys
  simp only [ENNReal.ofReal_eq_zero] at this
  exact hdet (abs_nonpos_iff.1 this)

/-- the regular zero set of a C¹ function on an open set is null -/
theorem regular_null (U : Set E) (hU : IsOpen U) (B : E → ℝ) (hB : ContDiffOn ℝ 1 B U) :
    μ {x | x ∈ U ∧ B x = 0 ∧ fderiv ℝ B x ≠ 0} = 0 := by
  apply measure_null_of_locally_null
  rintro x0 ⟨hx0, -, hL⟩
  obtain ⟨r, hr, h0⟩ := local_null μ U hU B hB x0 hx0 hL
  refine ⟨Metric.closedBall x0 r ∩ B ⁻¹' {0}, ?_, h0⟩
  have : Metric.closedBall x0 r ∈ 𝓝[{x | x ∈ U ∧ B x = 0 ∧ fderiv ℝ B x ≠ 0}] x0 :=
    nhdsWithin_le_nhds (Metric.closedBall_mem_nhds x0 hr)
  filter_upwards [this, self_mem_nhdsWithin] with y hy hy'
  exact ⟨hy, hy'.2.1⟩

end X6P20

open X6P20 in
theorem solution
    {d : ℕ} (hd : 0 < d) (U : Set (QAlgorithms.Papers.Independent.Dependency50.P20.Ambient d))
    (hU_open : IsOpen U) (hU_connected : IsConnected U)
    (B : QAlgorithms.Papers.Independent.Dependency50.P20.Ambient d → ℝ) (hB : AnalyticOnNhd ℝ B U) :
    volume (QAlgorithms.Papers.Independent.Dependency50.P20.regularZeroSet U B) = 0 := by
  apply measure_mono_null _ (regular_null volume U hU_open B (hB.contDiffOn hU_open.uniqueDiffOn))
  rintro x ⟨hx, h0, hg⟩
  refine ⟨hx, h0, fun hf => hg ?_⟩
  simp [gradient, hf]
