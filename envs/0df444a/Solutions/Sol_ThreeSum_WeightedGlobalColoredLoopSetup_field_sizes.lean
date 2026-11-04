-- Prove2me | solution 1 for ThreeSum.WeightedGlobalColoredLoopSetup.field_sizes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T02:17:31.823544+00:00
-- url     : https://prove2.me/submissions/b28e44fd-b335-48b9-bebe-b41cecf9b755

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryConcreteProfile
import Definitions.Def_Submission_Weighted_Global_TernaryArenaLoopState
import Definitions.Def_Submission_Weighted_Global_TernaryPreparedOriginals
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixPrepareAllocation
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSelectorAllocation
import Definitions.Def_Submission_Weighted_Global_TernaryColoredLoopSetup
import Theorems.Thm_ThreeSum_WeightedGlobalArenaPhaseBudget_field_sizes
import Theorems.Thm_ThreeSum_WeightedGlobalComputedExtensionMenu_field_card


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalColoredLoopSetup
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate
open WeightedGlobalConcreteProfile WeightedGlobalLocalParameters
set_option maxHeartbeats 4000000
set_option maxRecDepth 24000
variable {κ : ℕ}
variable (P : Profile κ) (n free menu c : ℕ) (A B C : List ℤ) (μ : ℕ→ℤ)
variable [Fact (Irreducible (WeightedGlobalComputedExtensionMenu.modulus P.p (dim P n) c))]
namespace ThreeSum.WeightedGlobalColoredLoopSetup
theorem _root_.solution :
    8*(J P n+2)*P.p^2≤Fintype.card (Extension P n c) ∧
    8*(J P n+2)*P.p^(2*(P.K+P.K))≤Fintype.card (Extension P n c) := by
  apply WeightedGlobalArenaPhaseBudget.field_sizes (J P n) P.K P.K_pos
  exact WeightedGlobalComputedExtensionMenu.field_card
end ThreeSum.WeightedGlobalColoredLoopSetup
