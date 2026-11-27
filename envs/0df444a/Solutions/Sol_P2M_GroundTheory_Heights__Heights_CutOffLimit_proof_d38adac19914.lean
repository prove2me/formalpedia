-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_CutOffLimit_proof_d38adac19914
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:54:34.381929+00:00
-- url     : https://prove2.me/submissions/22deba4f-d7da-42d3-9c62-10ef42c0d282

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCutOffLimit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCutOffDominated
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCutOffBoundaryBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCutOffLimit

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
open scoped ContDiff
namespace GroundTheory.Heights₂.Heights
namespace CutOffLimit
theorem _root_.solution (hC : CutOff.Statement) (hM : ChartMassCompact.Statement)
    (hD : CutOffDominated.Statement) (hB : CutOffBoundaryBound.Statement) :
    CutOffLimit.Statement := by
  intro n d J A P hJ hdim hA hP
  obtain ⟨χ, hχs, hχI, hχU, hχ1, hχE, hχM⟩ := hC n d J A P hJ hdim hA hP
  refine ⟨χ, hχs, hχU, fun F G φ hF hG hφ hc => ?_⟩
  have hcont : ∀ f, SmoothNear (zeroSet J) f → ContinuousOn f (zeroSet J) := by
    rintro f ⟨U, -, hU, hf⟩
    exact hf.continuousOn.mono hU
  have hcons : ∀ f, SmoothNear (zeroSet J) f → ∀ i, SmoothNear (zeroSet J) (vecCons f φ i) := by
    intro f hf i
    refine Fin.cases ?_ (fun i => ?_) i
    · simpa using hf
    · simpa using hφ i
  have hmeas : ∀ k, Measurable (χ k) := fun k => (hχs k).continuous.measurable
  refine ⟨hD n (d + 1) J A P χ F (vecCons G φ) hJ hdim hA hP hmeas hχI hχ1 (hcont F hF) (hcons G hG)
    (hM n (d + 1) J A F (vecCons G φ) hJ hdim hA (hcont F hF) (hcons G hG) (Or.inl hc)), ?_⟩
  have h1 := hD n (d + 1) J A P χ G (vecCons F φ) hJ hdim hA hP hmeas hχI hχ1 (hcont G hG) (hcons F hF)
    (hM n (d + 1) J A G (vecCons F φ) hJ hdim hA (hcont G hG) (hcons F hF) (Or.inr ⟨0, by simpa using hc⟩))
  obtain ⟨R, C, hRC⟩ := hB n d J A F G φ hJ hdim hA hF hG hφ hc
  have h0 : Tendsto (fun k => C * ((∫ y, chartAbsDens J A ((Metric.closedBall 0 R).indicator fun _ => 1)
      (vecCons (χ k) φ) y) + Real.sqrt (energyInt J A (Metric.closedBall 0 R) (χ k)))) atTop (𝓝 0) := by
    simpa using ((hχM R φ hφ).add (hχE R).sqrt).const_mul C
  refine h1.congr_dist (squeeze_zero (fun _ => dist_nonneg) (fun k => ?_) h0)
  rw [Real.dist_eq, abs_sub_comm]
  exact hRC (χ k) (hχs k)
end CutOffLimit
end GroundTheory.Heights₂.Heights
