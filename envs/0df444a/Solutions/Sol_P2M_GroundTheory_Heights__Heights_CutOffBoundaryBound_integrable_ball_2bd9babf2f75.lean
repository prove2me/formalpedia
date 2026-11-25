-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_CutOffBoundaryBound_integrable_ball_2bd9babf2f75
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:02:41.693223+00:00
-- url     : https://prove2.me/submissions/a124bf18-6827-4fab-bcf2-360f28db2e96

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCutOffBoundaryBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCutOffBoundaryParts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCutOff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCutOffGradient
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_OsgoodSeparate
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCutOffBoundaryBound
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_FibreBound_proof_4038dff927b3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CutOffGradient_proof_81aaa98bdfc1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CutOff_proof_fa25535eea0a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_RiemannExtensionSlices_proof_5560ddb795d4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SheetSumMeasurable_proof_de88497bcca1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_abs_chartDens_le_2f3f1c71cee6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_chartAbsDens_nonneg_5c6d71b76cc7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_sheetSum_le_mul_0df1d0f6a4b5


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open scoped ContDiff
noncomputable section
open GroundTheory.Heights₂.Heights.CutOffBoundaryBound
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights.CutOffBoundaryBound
theorem _root_.solution (hM : ChartMassCompact.Statement) {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {A : Matrix (Fin d) (Fin n) ℂ} (hJ : J.IsPrime) (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d)
    (hA : IsFiniteProjection J A) (R : ℝ) {w : (Fin n → ℂ) → ℝ} (hw : Continuous w)
    {ψ : Fin d → (Fin n → ℂ) → ℝ} (hψ : ∀ i, SmoothNear (zeroSet J) (ψ i)) :
    Integrable (chartAbsDens J A ((Metric.closedBall 0 R).indicator w) ψ) ∧
      Integrable (chartDens J A ((Metric.closedBall 0 R).indicator w) ψ) := by
  set b : (Fin n → ℂ) → ℝ := fun x => max (min 1 (R + 1 - ‖x‖)) 0 with hbdef
  have hbc : Continuous b := (continuous_const.min (continuous_const.sub continuous_norm)).max continuous_const
  have hbs : HasCompactSupport b := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : Fin n → ℂ) (R + 1)) fun x hx => ?_
    have hx' : R + 1 - ‖x‖ ≤ 0 := by
      simp only [Metric.mem_closedBall, dist_zero_right, not_le] at hx
      linarith
    simp [hbdef, min_eq_right (hx'.trans zero_le_one), max_eq_right hx']
  have hb1 : ∀ x ∈ Metric.closedBall (0 : Fin n → ℂ) R, b x = 1 := by
    intro x hx
    have hx' : 1 ≤ R + 1 - ‖x‖ := by
      simp only [Metric.mem_closedBall, dist_zero_right] at hx
      linarith
    simp [hbdef, min_eq_left hx']
  have hmeas : Measurable ((Metric.closedBall (0 : Fin n → ℂ) R).indicator w) :=
    hw.measurable.indicator Metric.isClosed_closedBall.measurableSet
  have hI := hM n d J A (fun x => b x * w x) ψ hJ hdim hA (hbc.mul hw).continuousOn hψ
    (Or.inl (show HasCompactSupport (b * w) from hbs.mul_right))
  have hm := SheetSumMeasurable.proof n d J A _ ψ hJ hdim hA hmeas hψ
  have hIA : Integrable (chartAbsDens J A ((Metric.closedBall 0 R).indicator w) ψ) := by
    refine hI.mono' hm.2.aestronglyMeasurable (Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (chartAbsDens_nonneg J A _ ψ y)]
    have hfin := (FibreBound.proof n d J A hJ hdim hA y).2.1
    have := sheetSum_le_mul hfin 1
      (fun x s => |(Metric.closedBall 0 R).indicator w x * maDens (fun k => ψ k ∘ s) y|)
      (fun x s => |b x * w x * maDens (fun k => ψ k ∘ s) y|) (fun x _ s _ => by
        by_cases hx : x ∈ Metric.closedBall (0 : Fin n → ℂ) R
        · rw [Set.indicator_of_mem hx, hb1 x hx, one_mul, one_mul]
        · rw [Set.indicator_of_notMem hx, zero_mul, abs_zero]
          positivity)
    simpa [chartAbsDens] using this
  exact ⟨hIA, hIA.mono' hm.1.aestronglyMeasurable
    (Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using abs_chartDens_le J A _ ψ y)⟩
end GroundTheory.Heights₂.Heights.CutOffBoundaryBound
