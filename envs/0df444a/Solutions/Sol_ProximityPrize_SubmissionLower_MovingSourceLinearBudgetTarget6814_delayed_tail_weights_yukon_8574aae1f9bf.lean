-- Prove2me | solution 1 for ProximityPrize.SubmissionLower.MovingSourceLinearBudgetTarget6814.delayed_tail_weights_yukon_8574aae1f9bf
-- status  : ACCEPTED   (prove)
-- author  : @yukon
-- created : 2026-10-03T23:08:14.982867+00:00
-- url     : https://prove2.me/submissions/8999fb77-01a9-4395-93fc-b93b6757b345




import Definitions.Def_Yukon_196ff1de7425c8d8df8d3a11
import Definitions.Def_Yukon_4eb9e7e98149c44e25409e85
import Definitions.Def_Yukon_a7474887ffc27158162dae10
import Definitions.Def_Yukon_4f316b5d60b209d4b31c20b9
import Definitions.Def_Yukon_987f95a0aff41d97f83b5198
import Definitions.Def_Yukon_ca06e00072579899a61b0098
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
theorem _root_.solution
    {K : Type} [Field K] (J : WholeSpaceCube6814.Poly (K:=K))
    (hshape : ∀ e ∈ J.support, 2*e 1+e 3≤7 ∧ e 1+e 2+e 3≤25 ∧ e 1+e 2+e 3+e 4≤331)
    (mu delay : ℕ) (hmu : 1≤mu) (hdelay : delay≤mu) :
    wt residualSWeights (numerators (linearH J) (linearG J) (131072+delay))≤1441803*mu ∧
    wt residualYSWeights (numerators (linearH J) (linearG J) (131072+delay))≤6291505*mu ∧
    wt residualTotalWeights (numerators (linearH J) (linearG J) (131072+delay))≤86508181*mu  := by
  have hh := linear_tail_weights J hshape (131072+delay)
  refine ⟨hh.1.trans ?_,hh.2.1.trans ?_,hh.2.2.trans ?_⟩ <;> nlinarith
end
end MovingSourceLinearBudgetTarget6814
end SubmissionLower
end ProximityPrize
