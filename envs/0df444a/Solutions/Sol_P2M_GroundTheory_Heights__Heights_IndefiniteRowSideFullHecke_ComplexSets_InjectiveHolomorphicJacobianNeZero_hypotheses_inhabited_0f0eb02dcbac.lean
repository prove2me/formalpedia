-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_InjectiveHolomorphicJacobianNeZero_hypotheses_inhabited_0f0eb02dcbac
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:58:22.186283+00:00
-- url     : https://prove2.me/submissions/20085fb1-c872-45c2-bc9b-b6800ff13fc1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StInjectiveHolomorphicOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StInjectiveHolomorphicJacobianNeZero
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_InjectiveHolomorphicOpen_hypotheses_inhabited_12237f493c3a


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
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace InjectiveHolomorphicJacobianNeZero
theorem _root_.solution :
    IsOpen (Metric.ball (0 : Fin 2 → ℂ) 1) ∧
      DifferentiableOn ℂ (fun t : Fin 2 → ℂ => ![t 0, t 1 + t 0 ^ 2]) (Metric.ball 0 1) ∧
      Set.InjOn (fun t : Fin 2 → ℂ => ![t 0, t 1 + t 0 ^ 2]) (Metric.ball 0 1) :=
  InjectiveHolomorphicOpen.hypotheses_inhabited
end InjectiveHolomorphicJacobianNeZero
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
