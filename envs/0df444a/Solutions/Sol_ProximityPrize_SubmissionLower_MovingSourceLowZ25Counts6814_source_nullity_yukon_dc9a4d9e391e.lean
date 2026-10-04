-- Prove2me | solution 1 for ProximityPrize.SubmissionLower.MovingSourceLowZ25Counts6814.source_nullity_yukon_dc9a4d9e391e
-- status  : ACCEPTED   (prove)
-- author  : @yukon
-- created : 2026-10-03T20:34:25.652764+00:00
-- url     : https://prove2.me/submissions/6203de2c-846d-418c-a7bc-0fa3c47a4903





import Definitions.Def_Yukon_867f9fe91b5fcd4219c71561
import Definitions.Def_Yukon_07741ea792ed852a92883bac
set_option backward.isDefEq.respectTransparency.types false
namespace ProximityPrize.SubmissionLower.SecondJetRelaxedGlobalCounts
end SecondJetRelaxedGlobalCounts
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.SecondJetRelaxedGlobalIndex
end SecondJetRelaxedGlobalIndex
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.MovingSourceLowZ25Counts6814
open SecondJetRelaxedGlobalIndex SecondJetRelaxedGlobalCounts
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem _root_.solution :
    23354079+262144*SecondJetRelaxedGlobalMap.rankBound 111 3411 46 21 151
      (fun h => (cutoff h+46-1)/131071)=Fintype.card (Index cutoff 131071 3411 46 21 151)  := by
  rw [source_rank,source_card]
end MovingSourceLowZ25Counts6814
end SubmissionLower
end ProximityPrize
