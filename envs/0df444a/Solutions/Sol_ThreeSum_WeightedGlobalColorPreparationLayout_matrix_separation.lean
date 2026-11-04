-- Prove2me | solution 1 for ThreeSum.WeightedGlobalColorPreparationLayout.matrix_separation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:10:28.956825+00:00
-- url     : https://prove2.me/submissions/9ce614aa-f860-4420-b910-c2ea8e45fd68

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryColorPreparation
import Definitions.Def_Submission_Weighted_Global_TernaryColorPreparationLayout

set_option autoImplicit false
open ThreeSum ThreeSum.WeightedGlobalColorPreparationLayout
open LightWeightedGlobalColorPreparation
set_option maxHeartbeats 1000000
namespace ThreeSum.WeightedGlobalColorPreparationLayout
theorem _root_.solution (free n W nA nB nC J : ℕ) :
    bMatrix free n W+nB*(J+2)=cMatrix free n W nB J ∧
    cMatrix free n W nB J+nC*(J+2)=carry free n W nA nB nC J ∧
    carry free n W nA nB nC J+2^J*(J+1)=positions free n W nA nB nC J ∧
    positions free n W nA nB nC J+nA*2^J=oMatrix free n W nA nB nC J :=
  ⟨rfl,rfl,rfl,rfl⟩
end ThreeSum.WeightedGlobalColorPreparationLayout
