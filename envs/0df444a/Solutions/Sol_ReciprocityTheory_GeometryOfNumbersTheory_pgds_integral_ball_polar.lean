-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.pgds_integral_ball_polar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:12:09.326919+00:00
-- url     : https://prove2.me/submissions/b28413fd-8952-4382-b959-656d834c054c

import Mathlib
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_DiscSt
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_pgds_cont_polar_symm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open MeasureTheory Filter Topology
open Set
namespace ReciprocityTheory.GeometryOfNumbersTheory
theorem _root_.solution {r : ℝ} (F : ℂ → ℝ) (hF : ContinuousOn F (Metric.closedBall 0 r)) :
    IntegrableOn (fun p : ℝ × ℝ => p.1 * F (Complex.polarCoord.symm p))
        (Ioo 0 r ×ˢ Ioo (-Real.pi) Real.pi) ∧
    ∫ z in Metric.ball (0 : ℂ) r, F z =
      ∫ s in Ioo 0 r, ∫ θ in Ioo (-Real.pi) Real.pi, s * F (Complex.polarCoord.symm (s, θ)) := by
  have hc := pgds_cont_polar_symm
  have hint : IntegrableOn (fun p : ℝ × ℝ => p.1 * F (Complex.polarCoord.symm p))
      (Icc 0 r ×ˢ Icc (-Real.pi) Real.pi) := by
    apply ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
    apply ContinuousOn.mul (continuous_fst.continuousOn)
    refine hF.comp hc.continuousOn ?_
    intro p hp
    simp only [Metric.mem_closedBall, dist_zero_right, Complex.norm_polarCoord_symm]
    rw [abs_of_nonneg hp.1.1]; exact hp.1.2
  have hint' := hint.mono_set (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)
  refine ⟨hint', ?_⟩
  have hpre : MeasurableSet ((fun p : ℝ × ℝ => Complex.polarCoord.symm p) ⁻¹' Metric.ball 0 r) :=
    hc.measurable Metric.isOpen_ball.measurableSet
  rw [← integral_indicator Metric.isOpen_ball.measurableSet, ← Complex.integral_comp_polarCoord_symm,
    polarCoord_target]
  have h1 : (fun p : ℝ × ℝ => p.1 • (Metric.ball (0:ℂ) r).indicator F (Complex.polarCoord.symm p)) =
      ((fun p : ℝ × ℝ => Complex.polarCoord.symm p) ⁻¹' Metric.ball 0 r).indicator
        (fun p : ℝ × ℝ => p.1 * F (Complex.polarCoord.symm p)) := by
    funext p
    by_cases hp : Complex.polarCoord.symm p ∈ Metric.ball (0:ℂ) r
    · rw [indicator_of_mem hp, indicator_of_mem (show p ∈ _ from hp), smul_eq_mul]
    · rw [indicator_of_notMem hp, indicator_of_notMem (show p ∉ _ from hp), smul_zero]
  rw [h1, setIntegral_indicator hpre]
  have h2 : Ioi (0:ℝ) ×ˢ Ioo (-Real.pi) Real.pi ∩
      ((fun p : ℝ × ℝ => Complex.polarCoord.symm p) ⁻¹' Metric.ball 0 r) =
      Ioo 0 r ×ˢ Ioo (-Real.pi) Real.pi := by
    ext p
    simp only [mem_inter_iff, mem_prod, mem_Ioi, mem_Ioo, mem_preimage, Metric.mem_ball,
      dist_zero_right, Complex.norm_polarCoord_symm]
    constructor
    · rintro ⟨⟨h0, hθ⟩, hr⟩; rw [abs_of_pos h0] at hr; exact ⟨⟨h0, hr⟩, hθ⟩
    · rintro ⟨⟨h0, hr⟩, hθ⟩; refine ⟨⟨h0, hθ⟩, ?_⟩; rw [abs_of_pos h0]; exact hr
  rw [h2, Measure.volume_eq_prod]
  rw [Measure.volume_eq_prod] at hint'
  exact setIntegral_prod _ hint'
end ReciprocityTheory.GeometryOfNumbersTheory
