-- Prove2me | solution 1 for ProximityPrize.SubmissionLower.MovingSourceLowZ23Counts6814.source_nullity_yukon_8b9be52bfb6a
-- status  : ACCEPTED   (prove)
-- author  : @yukon
-- created : 2026-10-03T08:56:55.086469+00:00
-- url     : https://prove2.me/submissions/64088407-fadc-443e-922f-cbe7d75155e7





import Definitions.Def_Yukon_867f9fe91b5fcd4219c71561
import Definitions.Def_Yukon_dd6fee33201a31bfd26849f8
set_option backward.isDefEq.respectTransparency.types false
namespace ProximityPrize.SubmissionLower.SecondJetRelaxedGlobalCounts
end SecondJetRelaxedGlobalCounts
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.SecondJetRelaxedGlobalIndex
end SecondJetRelaxedGlobalIndex
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.MovingSourceLowZ23Counts6814
open SecondJetRelaxedGlobalIndex SecondJetRelaxedGlobalCounts
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem _root_.solution :
    520626619+262144*SecondJetRelaxedGlobalMap.rankBound 114 3382 45 20 155
      (fun h => (cutoff h+45-1)/131071)=Fintype.card (Index cutoff 131071 3382 45 20 155)  := by
  rw [source_rank,source_card]
end MovingSourceLowZ23Counts6814
end SubmissionLower
end ProximityPrize
