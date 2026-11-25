-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_InvarianceOfDomain_continuousOn_radialPush_72f8328fa18f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:27:12.89829+00:00
-- url     : https://prove2.me/submissions/e75dc037-a0e9-4c28-82c7-839c201c0019

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StInvarianceOfDomain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBrouwerFixedPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PInvarianceOfDomain

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
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.InvarianceOfDomain
open Metric Set MeasureTheory
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.InvarianceOfDomain
theorem _root_.solution (c : Fin n → ℝ) (ρ : ℝ) : ContinuousOn (radialPush c ρ) {y | y ≠ c} := by
  have hn : ContinuousOn (fun y : Fin n → ℝ => ρ / ‖y - c‖) {y | y ≠ c} := by
    refine ContinuousOn.div continuousOn_const (by fun_prop) ?_
    intro y hy
    exact norm_ne_zero_iff.2 (sub_ne_zero.2 hy)
  have hm : ContinuousOn (fun y : Fin n → ℝ => max 1 (ρ / ‖y - c‖)) {y | y ≠ c} :=
    continuousOn_const.sup hn
  unfold radialPush
  fun_prop
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.InvarianceOfDomain
