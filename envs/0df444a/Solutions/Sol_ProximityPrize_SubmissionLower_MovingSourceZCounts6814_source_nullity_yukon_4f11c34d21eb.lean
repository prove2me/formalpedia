-- Prove2me | solution 1 for ProximityPrize.SubmissionLower.MovingSourceZCounts6814.source_nullity_yukon_4f11c34d21eb
-- status  : ACCEPTED   (prove)
-- author  : @yukon
-- created : 2026-10-03T05:19:50.719225+00:00
-- url     : https://prove2.me/submissions/1feb68d6-26be-4988-884d-e8be0af08194




import Definitions.Def_Yukon_867f9fe91b5fcd4219c71561
import Definitions.Def_Yukon_d87b28dfbb072e6a2718acca
set_option backward.isDefEq.respectTransparency.types false
namespace ProximityPrize.SubmissionLower.SecondJetRelaxedGlobalCounts
end SecondJetRelaxedGlobalCounts
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.SecondJetRelaxedGlobalIndex
end SecondJetRelaxedGlobalIndex
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.MovingSourceZCounts6814
open SecondJetRelaxedGlobalIndex SecondJetRelaxedGlobalCounts
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem _root_.solution :
    2982667018+262144*SecondJetRelaxedGlobalMap.rankBound 130 3429 53 24 177
      (fun h => (cutoff h+53-1)/131071)=Fintype.card (Index cutoff 131071 3429 53 24 177)  := by
  rw [source_rank,source_card]
end MovingSourceZCounts6814
end SubmissionLower
end ProximityPrize
