-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ProperSheetedFibreEsymm_proof_5cbcb8e575c9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:58:22.188583+00:00
-- url     : https://prove2.me/submissions/511e6274-e60e-4cf7-b626-6e8e8d2f465c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StProperSheetedFibreEsymm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StUnbranchedProperCountConstant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRiemannExtensionAnalytic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StParametricCircleIntegralAnalytic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PProperSheetedFibreEsymm
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ProperSheetedFibreEsymm_fibreEsymm_eq_51e9cd34a6ba
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ProperSheetedFibreEsymm_fibreEsymm_analyticAt_827979e2ede3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ProperSheetedFibreEsymm_fibreEsymm_locally_bounded_4ce462d07ee9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ProperSheetedFibreEsymm_analyticOnNhd_of_differentiableOn_617276966518

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
open Topology Filter Set Complex
open scoped Real
open ProperSheetedFibreEsymm
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace ProperSheetedFibreEsymm
theorem _root_.solution (hcount : UnbranchedProperCountConstant.Statement)
    (hriem : RiemannExtensionAnalytic.Statement) (hcirc : ParametricCircleIntegralAnalytic.Statement) :
    ProperSheetedFibreEsymm.Statement := by
  intro σ _ Y d A D δ l j hD _ hprop hδ hW hchart
  obtain ⟨F, hFd, hFeq⟩ := hriem d D δ (fibreEsymm Y A l j) hD hδ.differentiableOn hW
    (fun t ht => (fibreEsymm_analyticAt l j hD hprop hchart ht.1 ht.2).differentiableAt.differentiableWithinAt)
    (fun τ hτ => fibreEsymm_locally_bounded hcount l j hD hprop hδ hchart hτ)
  refine ⟨F, analyticOnNhd_of_differentiableOn hcirc hD hFd, fun t ht hδt s hs => ?_⟩
  rw [hFeq ⟨ht, hδt⟩, fibreEsymm_eq s hs]
end ProperSheetedFibreEsymm
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
