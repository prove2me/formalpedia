-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaSelectorAllocation.initial_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:19:07.17377+00:00
-- url     : https://prove2.me/submissions/634a22a3-9c0b-43b4-bd4f-6ada7b728f9f

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaCandidateScoreBounds
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSelectorAllocation

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaSelectorAllocation
open Light WeightedGlobalArenaPrefixFootprints WeightedGlobalArenaAllocation WeightedGlobalArenaLayout
open WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters
variable {p m F : ℕ} [Fact p.Prime]
set_option maxHeartbeats 6000000
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaSelectorAllocation
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
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaSelectorAllocation
