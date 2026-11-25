-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartMassCompact_integrable_ball_09c7bd6a1abc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:17:51.812119+00:00
-- url     : https://prove2.me/submissions/d802ddb6-ade9-448e-b902-147c7b54c8ee

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFibreBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCutOff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PChartMassCompact
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_FibreBound_proof_4038dff927b3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CutOff_proof_fa25535eea0a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SheetSumMeasurable_proof_de88497bcca1


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
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ENNReal
noncomputable section
open GroundTheory.Heights₂.Heights.ChartMassCompact
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights.ChartMassCompact
theorem _root_.solution (hC : ChartMassCompare.Statement) (hMF : MassFinite.Statement)
    (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ) (ψ : Fin d → (Fin n → ℂ) → ℝ)
    (hJ : J.IsPrime) (hd : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d)
    (hA : IsFiniteProjection J A) (hψ : ∀ k, SmoothNear (zeroSet J) (ψ k)) (R : ℝ) :
    Integrable (chartAbsDens J A ((Metric.closedBall (0 : Fin n → ℂ) R).indicator fun _ => (1 : ℝ)) ψ) := by
  obtain ⟨K, hK, hle⟩ := hC n d J A ψ R hJ hd hA hψ
  have hmeas := (SheetSumMeasurable.proof n d J A
    ((Metric.closedBall (0 : Fin n → ℂ) R).indicator fun _ => (1 : ℝ)) ψ hJ hd hA
    (measurable_const.indicator Metric.isClosed_closedBall.measurableSet) hψ).2
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  have hbd : Bornology.IsBounded
      (WithLp.ofLp ⁻¹' Metric.closedBall (0 : Fin n → ℂ) R : Set (EuclideanSpace ℂ (Fin n))) :=
    (PiLp.antilipschitzWith_ofLp 2 fun _ : Fin n => ℂ).isBounded_preimage Metric.isBounded_closedBall
  obtain ⟨R', hR'⟩ := (Metric.isBounded_iff_subset_ball 0).1 hbd
  have h1 := hle (fun _ => 1) measurable_const
  simp only [enorm_one, setLIntegral_one] at h1
  refine h1.trans_lt (ENNReal.mul_lt_top hK ?_)
  exact (measure_mono (Set.inter_subset_inter_right _ hR')).trans_lt (hMF n d J hJ hd R')
end GroundTheory.Heights₂.Heights.ChartMassCompact
