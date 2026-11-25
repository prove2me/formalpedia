-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_FiniteTwists_proof_4ffbf9f6a4ae
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:27:49.557564+00:00
-- url     : https://prove2.me/submissions/aac60b34-91f3-4a96-af7a-764e1f303b78

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PFiniteTwists

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
universe u w
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace FiniteTwists
theorem _root_.solution (hT1 : TwistFinite.Statement.{u, w}) : FiniteTwists.Statement.{u, w} :=
  hT1
end FiniteTwists
end GroundTheory.Heights₂.Heights.Kleiman
