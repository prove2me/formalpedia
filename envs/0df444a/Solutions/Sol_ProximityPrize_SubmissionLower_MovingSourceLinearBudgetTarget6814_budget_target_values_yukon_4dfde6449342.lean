-- Prove2me | solution 1 for ProximityPrize.SubmissionLower.MovingSourceLinearBudgetTarget6814.budget_target_values_yukon_4dfde6449342
-- status  : ACCEPTED   (prove)
-- author  : @yukon
-- created : 2026-10-03T23:07:56.158136+00:00
-- url     : https://prove2.me/submissions/18cd02ba-5330-491c-b1bc-9643e6344c67




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
    properRectangleTarget=91885113709214910 ∧
    denominatorHelperTarget=3067534234414 ∧
    constantParameterTarget=6172311564  := by decide +kernel
end
end MovingSourceLinearBudgetTarget6814
end SubmissionLower
end ProximityPrize
