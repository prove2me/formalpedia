-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AuslanderBuchsbaumProjDimUpper_proof_8df0a829317e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:54:55.324741+00:00
-- url     : https://prove2.me/submissions/ea14c624-43b3-4f16-b808-7c1be729c862

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAuslanderBuchsbaumProjDimUpper
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_AuslanderBuchsbaumDepthBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PAuslanderBuchsbaumProjDimUpper
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_hasProjectiveDimensionLE_sub_length_of_isWeaklyRegular_525a8eaee0ce

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
open IsLocalRing CategoryTheory RingTheory.Sequence
universe u
namespace GroundTheory.Heights₂.Heights
namespace AuslanderBuchsbaumProjDimUpper
theorem _root_.solution : AuslanderBuchsbaumProjDimUpper.Statement := by
  intro R _ _ _ M _ _ _ _ n d ms hM hd hms hreg
  exact hasProjectiveDimensionLE_sub_length_of_isWeaklyRegular R d hd ms M n hM hms hreg
end AuslanderBuchsbaumProjDimUpper
end GroundTheory.Heights₂.Heights
