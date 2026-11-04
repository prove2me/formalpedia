-- Prove2me | solution 1 for ThreeSum.WeightedGlobalColorPreparationLayout.matrices_before_work
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:10:23.341351+00:00
-- url     : https://prove2.me/submissions/aa7ee2dd-3f71-4107-bde0-ef62a776df75

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryColorPreparation
import Definitions.Def_Submission_Weighted_Global_TernaryColorPreparationLayout

set_option autoImplicit false
open ThreeSum ThreeSum.WeightedGlobalColorPreparationLayout
open LightWeightedGlobalColorPreparation
set_option maxHeartbeats 1000000
namespace ThreeSum.WeightedGlobalColorPreparationLayout
theorem _root_.solution (free n W nA nB nC J : ℕ) :
    bMatrix free n W+nB*(J+2)≤work free n W nA nB nC J ∧
    cMatrix free n W nB J+nC*(J+2)≤work free n W nA nB nC J ∧
    oMatrix free n W nA nB nC J+nA*2^J*(J+2)≤work free n W nA nB nC J ∧
    positions free n W nA nB nC J+nA*2^J≤work free n W nA nB nC J ∧
    carry free n W nA nB nC J+2^J*(J+1)≤work free n W nA nB nC J := by
  unfold work oMatrix positions carry cMatrix bMatrix
  omega
end ThreeSum.WeightedGlobalColorPreparationLayout
