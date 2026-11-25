-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ParametricCircleIntegralAnalytic_analyticOnNhd_of_differentiableOn_fd_37006865feb4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:07:50.071512+00:00
-- url     : https://prove2.me/submissions/d54d1d37-f735-4d9e-a307-a0f78424c209

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StParametricCircleIntegralAnalytic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRiemannExtensionAnalytic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PParametricCircleIntegralAnalytic
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_RiemannExtensionAnalytic_analyticOnNhd_of_differentiableOn_c966cce3f6fd


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open Metric Filter Topology Set Complex MeasureTheory
open scoped Real
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.ParametricCircleIntegralAnalytic
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.ParametricCircleIntegralAnalytic
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] {O : Set E} {f : E → ℂ} (hO : IsOpen O) (hf : DifferentiableOn ℂ f O) :
    AnalyticOnNhd ℂ f O := by
  let e : E ≃L[ℂ] (Fin (Module.finrank ℂ E) → ℂ) :=
    ContinuousLinearEquiv.ofFinrankEq (Module.finrank_fin_fun ℂ).symm
  have hO' : IsOpen (e.symm ⁻¹' O) := hO.preimage e.symm.continuous
  have hg : DifferentiableOn ℂ (f ∘ e.symm) (e.symm ⁻¹' O) :=
    hf.comp e.symm.differentiableOn (fun y hy => hy)
  have ha := RiemannExtensionAnalytic.analyticOnNhd_of_differentiableOn hO' hg
  intro x hx
  have h1 : AnalyticAt ℂ (f ∘ e.symm) (e x) := ha (e x) (by simpa using hx)
  have h2 := h1.comp (ContinuousLinearMap.analyticAt (e : E →L[ℂ] (Fin (Module.finrank ℂ E) → ℂ)) x)
  simpa [Function.comp_def] using h2
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.ParametricCircleIntegralAnalytic
