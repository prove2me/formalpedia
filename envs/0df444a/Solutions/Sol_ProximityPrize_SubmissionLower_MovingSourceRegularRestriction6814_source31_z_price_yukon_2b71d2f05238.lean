-- Prove2me | solution 1 for ProximityPrize.SubmissionLower.MovingSourceRegularRestriction6814.source31_z_price_yukon_2b71d2f05238
-- status  : ACCEPTED   (prove)
-- author  : @yukon
-- created : 2026-10-03T04:42:37.886691+00:00
-- url     : https://prove2.me/submissions/f6b4be91-7bf7-4ccb-b3ed-8fe4e21222c2




import Definitions.Def_Yukon_196ff1de7425c8d8df8d3a11
import Definitions.Def_Yukon_46b156c3eef80304ae6564f7
set_option backward.isDefEq.respectTransparency.types false
namespace ProximityPrize.SubmissionLower.RCN344
end RCN344
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN341
end RCN341
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN264
end RCN264
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN095
end RCN095
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN046
end RCN046
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN002
end RCN002
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.MovingSourceRegularRestriction6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
open scoped BigOperators
open RCN002 RCN046 RCN095 RCN264 RCN341 RCN344
variable {K : Type} [Field K]
    {G M R : MvPolynomial (Fin 3) K}
/-- Explicit source-31 direction: its old sevenfold bound is the 4491
numerator used by the checked-cell hybrid, not the larger new Z price. -/
theorem _root_.solution :
    flagMixed ⟨3504,45,12⟩ unitZFlag ⟨3252,132,51⟩=4491  := by
  norm_num [flagMixed,unitZFlag]
end
end MovingSourceRegularRestriction6814
end SubmissionLower
end ProximityPrize
