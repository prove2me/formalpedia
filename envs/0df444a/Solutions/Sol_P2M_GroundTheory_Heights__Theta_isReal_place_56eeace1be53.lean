-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_isReal_place_56eeace1be53
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:13:47.360622+00:00
-- url     : https://prove2.me/submissions/4b2f977b-297a-40ad-aa8d-2a84d254bd86

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_QuadraticConj
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_CMDatum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open NumberField GroundTheory.Automorphic
variable (F E : Type*) [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E]
  [IsTotallyComplex E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {F E}
variable (F E)
variable {F E}
variable (F E)
omit [NumberField F]
variable {F}
namespace GroundTheory.Heights₂.Theta
theorem _root_.solution (v : InfinitePlace F) : v.IsReal := IsTotallyReal.isReal v
end GroundTheory.Heights₂.Theta
