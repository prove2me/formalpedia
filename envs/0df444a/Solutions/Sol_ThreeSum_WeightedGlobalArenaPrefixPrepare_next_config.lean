-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaPrefixPrepare.next_config
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T23:17:50.777586+00:00
-- url     : https://prove2.me/submissions/dd15cf19-202a-4836-bde3-f25ae8855136

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryPrefixSeedHeader
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceSetup
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSeedCandidate
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixPrepare

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaPrefixPrepare
open Light WeightedGlobalLocalParameters TernaryJointType WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup
open LightWeightedGlobalPrefixStep
set_option maxHeartbeats 1000000
set_option maxRecDepth 24000
namespace ThreeSum.WeightedGlobalArenaPrefixPrepare
theorem _root_.solution (p m F j J n U0 a b scale : ℕ) (I : Input)
    (A : WeightedGlobalArenaSeedCandidate.Inputs) (Q : WeightedGlobalGoodOutputCatalog.Output m)
    (hJ : J=A.J) :
    WeightedGlobalPrefixSeedHeader.nextConfig (WeightedGlobalArenaSeedCandidate.config p j I A 0)
      (inputs p m F j J n U0 a b scale I Q)=WeightedGlobalArenaSeedCandidate.config p (j+1) I A 0 :=by
  cases hJ
  rfl
end ThreeSum.WeightedGlobalArenaPrefixPrepare
