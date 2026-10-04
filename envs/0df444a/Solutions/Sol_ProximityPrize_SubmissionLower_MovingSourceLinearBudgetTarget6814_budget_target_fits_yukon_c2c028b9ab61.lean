-- Prove2me | solution 1 for ProximityPrize.SubmissionLower.MovingSourceLinearBudgetTarget6814.budget_target_fits_yukon_c2c028b9ab61
-- status  : ACCEPTED   (prove)
-- author  : @yukon
-- created : 2026-10-03T23:09:53.016424+00:00
-- url     : https://prove2.me/submissions/23625a4a-732a-4b73-8689-65bbccae3633




import Definitions.Def_Yukon_a7474887ffc27158162dae10
set_option backward.isDefEq.respectTransparency.types false
namespace ProximityPrize.SubmissionLower.MovingSourceReducedTailWeights6814
end MovingSourceReducedTailWeights6814
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.MovingSourceFlowNumerator6814
end MovingSourceFlowNumerator6814
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.MovingSourceLinearFlow6814
end MovingSourceLinearFlow6814
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN156
end RCN156
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN234
end RCN234
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.MovingSourceLinearBudgetTarget6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 300000
open RCN234 RCN156
open MovingSourceLinearFlow6814 MovingSourceFlowNumerator6814 MovingSourceReducedTailWeights6814
theorem _root_.solution :
    properRectangleTarget+denominatorHelperTarget+constantParameterTarget+tangentTarget=
      93691085521379248 ∧
    properRectangleTarget+denominatorHelperTarget+constantParameterTarget+tangentTarget<
      272069082261391681  := by decide +kernel
end
end MovingSourceLinearBudgetTarget6814
end SubmissionLower
end ProximityPrize
