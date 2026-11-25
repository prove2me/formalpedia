-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_TangentGraphLowerDensity_inPart_eq_toLp_833bbaba1b13
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:20:55.127076+00:00
-- url     : https://prove2.me/submissions/7c65ad28-9811-4403-97a2-86340be7cff0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTangentGraphLowerDensity
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StVarietyLelongMono
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PTangentGraphLowerDensity
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_TangentGraphLowerDensity_inPart_apply_572a6cb21cc2

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
open MeasureTheory Filter Topology
open scoped ENNReal
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace TangentGraphLowerDensity
theorem _root_.solution {n : ℕ}
    (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n))) (I : Finset (Fin n))
    (z : EuclideanSpace ℂ (Fin n)) :
    TangentGraphLowerDensity.inPart b I z = WithLp.toLp 2 (frameProj b I z) := by
  refine PiLp.ext fun i => ?_
  simp [TangentGraphLowerDensity.inPart_apply, frameProj]
end TangentGraphLowerDensity
end GroundTheory.Heights₂.Heights
