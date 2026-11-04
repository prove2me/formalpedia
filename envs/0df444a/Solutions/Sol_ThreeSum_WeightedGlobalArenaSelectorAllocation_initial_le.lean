-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaSelectorAllocation.initial_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T22:24:54.562965+00:00
-- url     : https://prove2.me/submissions/226791d7-354f-4798-bdcc-352aeff5cc3e

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaCandidateScoreBounds
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSelectorAllocation

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaSelectorAllocation
open Light WeightedGlobalArenaPrefixFootprints WeightedGlobalArenaAllocation WeightedGlobalArenaLayout
open WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters
variable {p m F : ℕ} [Fact p.Prime]
set_option maxHeartbeats 6000000
namespace ThreeSum.WeightedGlobalArenaSelectorAllocation
theorem _root_.solution {K b n J nO nO' : ℕ} (hO : nO≤nO') (a drift scale : ℕ) :
    LightTernaryInitialBudgets.initial K b n J nO≤
      LightTernaryInitialBudgets.word K b a drift scale n J nO' := by
  have hh : LightTernaryInitialBudgets.initial K b n J nO≤
      LightTernaryInitialBudgets.initial K b n J nO' := by
    unfold LightTernaryInitialBudgets.initial
    gcongr
  apply hh.trans
  unfold LightTernaryInitialBudgets.word
  omega
end ThreeSum.WeightedGlobalArenaSelectorAllocation
