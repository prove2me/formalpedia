-- Prove2me | solution 1 for PI.RhsWLim.W.chartJac
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:15:40.419534+00:00
-- url     : https://prove2.me/submissions/a36581b8-3360-4b7a-8dab-30ebbab8d3e4

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_ChartLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_ChartJac
import Theorems.Thm_PI_RhsWLim_W_chartLim


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal
open PI PI.RhsWLim PI.RhsWLim.W
namespace PI.RhsWLim.W
theorem _root_.solution : ChartJac := by
  intro E _ _ _ _ _ _ Φ ν δ hΦ hdet hδ hδtop hU
  obtain ⟨U, hU, hνU⟩ := hU
  have hstrict : HasStrictFDerivAt Φ
      ((ContinuousLinearMap.toContinuousLinearEquivOfDetNeZero (fderiv ℝ Φ 0) hdet : E ≃L[ℝ] E) :
        E →L[ℝ] E) 0 := by
    rw [ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero]
    exact hΦ.hasStrictFDerivAt (by norm_num)
  have hsrc : (hstrict.toOpenPartialHomeomorph Φ).source ∈ 𝓝 (0 : E) :=
    (hstrict.toOpenPartialHomeomorph Φ).open_source.mem_nhds hstrict.mem_toOpenPartialHomeomorph_source
  have hev : ∀ᶠ y in 𝓝 (0 : E), ContDiffAt ℝ 1 Φ y := hΦ.eventually (by simp)
  have hUpre : Φ ⁻¹' U ∈ 𝓝 (0 : E) := hΦ.continuousAt.preimage_mem_nhds hU
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem (Filter.inter_mem hsrc hev) hUpre)
  have hcont : ContinuousAt (fun x => ENNReal.ofReal |(fderiv ℝ Φ x).det| * δ (Φ x)) 0 := by
    have hA : ContinuousAt (fun x => ENNReal.ofReal |(fderiv ℝ Φ x).det|) 0 :=
      ENNReal.continuous_ofReal.continuousAt.comp (continuous_abs.continuousAt.comp
        (ContinuousLinearMap.continuous_det.continuousAt.comp (hΦ.continuousAt_fderiv (by norm_num))))
    have hB : ContinuousAt (fun x => δ (Φ x)) 0 := hδ.comp hΦ.continuousAt
    exact ENNReal.Tendsto.mul hA (Or.inr hδtop) hB (Or.inr ENNReal.ofReal_ne_top)
  have hntop : ENNReal.ofReal |(fderiv ℝ Φ 0).det| * δ (Φ 0) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hδtop
  have heq : ∀ ρ : ℝ, 0 < ρ → ρ < ε → ν (Φ '' Metric.ball 0 ρ) =
      ∫⁻ x in Metric.ball 0 ρ, ENNReal.ofReal |(fderiv ℝ Φ x).det| * δ (Φ x) := by
    intro ρ _ hρε
    have hsub : Metric.ball (0 : E) ρ ⊆ Metric.ball 0 ε := Metric.ball_subset_ball hρε.le
    have hinj : Set.InjOn Φ (Metric.ball 0 ρ) := by
      rw [← hstrict.toOpenPartialHomeomorph_coe]
      exact (hstrict.toOpenPartialHomeomorph Φ).injOn.mono fun x hx => (hball (hsub hx)).1.1
    have hcd : ∀ x ∈ Metric.ball (0 : E) ρ, ContDiffAt ℝ 1 Φ x := fun x hx => (hball (hsub hx)).1.2
    have hdiff : ∀ x ∈ Metric.ball (0 : E) ρ,
        HasFDerivWithinAt Φ (fderiv ℝ Φ x) (Metric.ball 0 ρ) x := fun x hx =>
      ((hcd x hx).differentiableAt one_ne_zero).hasFDerivAt.hasFDerivWithinAt
    have hcon : ContinuousOn Φ (Metric.ball 0 ρ) := fun x hx =>
      (hcd x hx).continuousAt.continuousWithinAt
    have hmeas : MeasurableSet (Φ '' Metric.ball 0 ρ) :=
      Metric.isOpen_ball.measurableSet.image_of_continuousOn_injOn hcon hinj
    have himg : Φ '' Metric.ball 0 ρ ⊆ U := by
      rintro _ ⟨x, hx, rfl⟩
      exact (hball (hsub hx)).2
    rw [hνU _ himg hmeas]
    exact MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul volume
      Metric.isOpen_ball.measurableSet hdiff hinj δ
  have hlim := chartLim E E Φ ν (fun x => ENNReal.ofReal |(fderiv ℝ Φ x).det| * δ (Φ x)) hcont hntop
    ⟨ε, hε, heq⟩
  have h0 : (ENNReal.ofReal |(fderiv ℝ Φ 0).det| * δ (Φ 0)).toReal =
      (δ (Φ 0)).toReal * |(fderiv ℝ Φ 0).det| := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _), mul_comm]
  rw [← h0]
  exact hlim
end PI.RhsWLim.W
