-- Prove2me | solution 1 for ProximityPrize.SubmissionLower.MovingSourceReducedTailWeights6814.first_tail_weights_yukon_3ba04dd88007
-- status  : ACCEPTED   (prove)
-- author  : @yukon
-- created : 2026-10-03T20:32:32.925142+00:00
-- url     : https://prove2.me/submissions/89a6c28a-9672-497e-aa14-6bd8702199a2




import Definitions.Def_Yukon_196ff1de7425c8d8df8d3a11
import Definitions.Def_Yukon_4eb9e7e98149c44e25409e85
import Definitions.Def_Yukon_4f316b5d60b209d4b31c20b9
import Definitions.Def_Yukon_987f95a0aff41d97f83b5198
import Definitions.Def_Yukon_ca06e00072579899a61b0098
set_option backward.isDefEq.respectTransparency.types false
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
namespace MvPolynomial
end MvPolynomial
namespace ProximityPrize.SubmissionLower.MovingSourceReducedTailWeights6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 300000
open MvPolynomial RCN234 RCN156
open MovingSourceLinearFlow6814 MovingSourceFlowNumerator6814
variable {K : Type} [Field K]
local notation "Poly" => MvPolynomial (Fin 4) K
theorem _root_.solution
    (J : WholeSpaceCube6814.Poly (K:=K))
    (hshape : ∀ e ∈ J.support, 2*e 1+e 3≤7 ∧ e 1+e 2+e 3≤25 ∧ e 1+e 2+e 3+e 4≤331) :
    wt residualSWeights (numerators (linearH J) (linearG J) 131072)≤1441792 ∧
    wt residualYSWeights (numerators (linearH J) (linearG J) 131072)≤6291457 ∧
    wt residualTotalWeights (numerators (linearH J) (linearG J) 131072)≤86507521  := by
  exact linear_tail_weights J hshape 131072
end
end MovingSourceReducedTailWeights6814
end SubmissionLower
end ProximityPrize
