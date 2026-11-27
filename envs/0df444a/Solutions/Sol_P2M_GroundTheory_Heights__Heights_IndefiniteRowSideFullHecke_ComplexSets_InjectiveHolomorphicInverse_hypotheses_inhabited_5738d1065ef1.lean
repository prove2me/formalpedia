-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_InjectiveHolomorphicInverse_hypotheses_inhabited_5738d1065ef1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:58:18.028274+00:00
-- url     : https://prove2.me/submissions/4d070b78-7224-4387-aad0-8a6c8f32b802

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StInjectiveHolomorphicOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StInjectiveHolomorphicInverse
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
namespace InjectiveHolomorphicInverse
theorem _root_.solution :
    IsOpen (Metric.ball (0 : Fin 2 → ℂ) 1) ∧
      DifferentiableOn ℂ (fun t : Fin 2 → ℂ => ![t 0, t 1 + t 0 ^ 2]) (Metric.ball 0 1) ∧
      Set.InjOn (fun t : Fin 2 → ℂ => ![t 0, t 1 + t 0 ^ 2]) (Metric.ball 0 1) :=
  InjectiveHolomorphicOpen.hypotheses_inhabited
end InjectiveHolomorphicInverse
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
