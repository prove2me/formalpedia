-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PlaceCentredSum_neg_log_apply_dfa8e9f4105e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:25:14.898214+00:00
-- url     : https://prove2.me/submissions/19f237f6-b77e-41cd-8fdf-3c3819c2631c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightPlaceCentredSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_PPlaceCentredSum
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PlaceCentredSum_apply_algebraMap_fc47d50d1873

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
open NumberField IsDedekindDomain Ideal
open GroundTheory.Heights₂.Heights.PlaceCentredSum
variable {L K : Type} [Field L] [NumberField L] [Field K] [NumberField K] [Algebra L K]
namespace GroundTheory.Heights₂.Heights.PlaceCentredSum
theorem _root_.solution (v : FinitePlace K) (t : L) :
    -Real.log (v (algebraMap L K t)) = deg L v * -Real.log (FinitePlace.mk (below v) t) := by
  rw [apply_algebraMap, Real.log_pow]
  ring
end GroundTheory.Heights₂.Heights.PlaceCentredSum
