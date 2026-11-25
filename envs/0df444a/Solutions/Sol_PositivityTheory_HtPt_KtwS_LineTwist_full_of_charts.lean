-- Prove2me | solution 1 for PositivityTheory.HtPt.KtwS.LineTwist.full_of_charts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:59:00.943448+00:00
-- url     : https://prove2.me/submissions/53f15177-538a-438c-b8f8-5be327229cbb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_AssemblyBase
import Definitions.Def_Development_WeilBound_CoreStatements_HodgeTatePoints_ExistsLineBundleTwistMulOf
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PClaimVanish
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleNefPlusAmple
import Definitions.Def_Development_WeilBound_CoreStatements_HodgeTatePoints_FullOfCharts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory PositivityTheory.HtPt PositivityTheory.HtPt.KtwS
open GroundTheory.Heights₂.Heights.Kleiman
universe u v w
namespace PositivityTheory.HtPt.KtwS
namespace LineTwist
theorem _root_.solution : LineTwist.Statement.{u, w} :=
  fun _ _ _ _ _ _ _ Q₁ Q₂ => ⟨KThm.lbTwist Q₁ Q₂, rfl⟩
end LineTwist
end PositivityTheory.HtPt.KtwS
