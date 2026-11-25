-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PuncturedBranchSameOrder_const_mem_ball_iff_5c748a61eaf1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:48:11.381048+00:00
-- url     : https://prove2.me/submissions/acdeb8f7-4ea8-422f-bbe0-51380b2f1d1f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPuncturedBranchSameOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPuncturedCurveDiscInverse
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPuncturedBranchSameOrder

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
open MvPolynomial ComplexSets Filter Topology
noncomputable section
open GroundTheory.Heights₂.Heights.PuncturedBranchSameOrder
namespace GroundTheory.Heights₂.Heights.PuncturedBranchSameOrder
theorem _root_.solution (τ : ℂ) (r : ℝ) :
    (fun _ : Fin 1 ↦ τ) ∈ Metric.ball (0 : Fin 1 → ℂ) r ↔ τ ∈ Metric.ball (0 : ℂ) r := by
  simp only [Metric.mem_ball, dist_zero_right, pi_norm_const]
end GroundTheory.Heights₂.Heights.PuncturedBranchSameOrder
