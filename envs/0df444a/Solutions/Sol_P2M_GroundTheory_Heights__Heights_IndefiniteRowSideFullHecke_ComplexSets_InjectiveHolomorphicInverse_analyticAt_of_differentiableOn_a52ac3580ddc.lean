-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_InjectiveHolomorphicInverse_analyticAt_of_differentiableOn_a52ac3580ddc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:55:35.879429+00:00
-- url     : https://prove2.me/submissions/a6ebfffa-a976-4f48-8af1-31355a75b991

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StInjectiveHolomorphicInverse
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StInjectiveHolomorphicJacobianNeZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_OsgoodSeparate
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PInjectiveHolomorphicInverse
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_analyticOnNhd_of_continuousOn_of_separately_ff52795ca853


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
open Filter Topology
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.InjectiveHolomorphicInverse
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.InjectiveHolomorphicInverse
theorem _root_.solution {k : ℕ} {U : Set (Fin k → ℂ)} {f : (Fin k → ℂ) → Fin k → ℂ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) {x : Fin k → ℂ} (hx : x ∈ U) : AnalyticAt ℂ f x := by
  refine AnalyticAt.pi fun i => ?_
  refine analyticOnNhd_of_continuousOn_of_separately hU
    ((continuous_apply i).comp_continuousOn hf.continuousOn) (fun z hz j => ?_) x hx
  have hfz : DifferentiableAt ℂ (fun w => f w i) z :=
    differentiableAt_pi.mp (hf.differentiableAt (hU.mem_nhds hz)) i
  have hu : DifferentiableAt ℂ (Function.update z j) (z j) :=
    (hasFDerivAt_update z (z j)).differentiableAt
  have hfz' : DifferentiableAt ℂ (fun w => f w i) (Function.update z j (z j)) := by
    rwa [Function.update_eq_self]
  exact hfz'.comp (z j) hu
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.InjectiveHolomorphicInverse
