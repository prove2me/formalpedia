-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PlaceCentredSum_deg_ne_zero_16fd8e505679
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:47:26.039246+00:00
-- url     : https://prove2.me/submissions/72c3c06a-0050-4ce5-bf9f-10f732252690

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightPlaceCentredSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_PPlaceCentredSum

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
theorem _root_.solution (v : FinitePlace K) : deg L v ≠ 0 := by
  refine mul_ne_zero ?_ (inertiaDeg_pos _ _).ne'
  rw [← ramificationIdx'_eq_ramificationIdx _ _ (below (L := L) v).ne_bot]
  exact IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver _ (below v).ne_bot
end GroundTheory.Heights₂.Heights.PlaceCentredSum
