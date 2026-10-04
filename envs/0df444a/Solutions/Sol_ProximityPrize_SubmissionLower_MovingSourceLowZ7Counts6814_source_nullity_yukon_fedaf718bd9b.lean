-- Prove2me | solution 1 for ProximityPrize.SubmissionLower.MovingSourceLowZ7Counts6814.source_nullity_yukon_fedaf718bd9b
-- status  : ACCEPTED   (prove)
-- author  : @yukon
-- created : 2026-10-03T05:35:23.020132+00:00
-- url     : https://prove2.me/submissions/c6f35f76-5115-4d92-95c3-0be6b6fc2e22




import Definitions.Def_Yukon_867f9fe91b5fcd4219c71561
import Definitions.Def_Yukon_60d896ce8f2a3dcef6c392c5
set_option backward.isDefEq.respectTransparency.types false
namespace ProximityPrize.SubmissionLower.SecondJetRelaxedGlobalCounts
end SecondJetRelaxedGlobalCounts
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.SecondJetRelaxedGlobalIndex
end SecondJetRelaxedGlobalIndex
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.MovingSourceLowZ7Counts6814
open SecondJetRelaxedGlobalIndex SecondJetRelaxedGlobalCounts
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem _root_.solution :
    179953401+262144*SecondJetRelaxedGlobalMap.rankBound 114 3043 47 21 154
      (fun h => (cutoff h+47-1)/131071)=Fintype.card (Index cutoff 131071 3043 47 21 154)  := by
  rw [source_rank,source_card]
end MovingSourceLowZ7Counts6814
end SubmissionLower
end ProximityPrize
