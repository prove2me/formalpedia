-- Prove2me | solution 1 for ThreeSum.SourceBandBanksCosts.overhead_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:22:43.386753+00:00
-- url     : https://prove2.me/submissions/14d030f6-e4c5-4f74-8f15-120f5c32c547

import Definitions.Def_Submission_ThreeSum_LightSourceBandBanksProgram
import Definitions.Def_Submission_ThreeSum_SourceBandPairCosts
import Definitions.Def_Submission_ThreeSum_SourceBandBanksCosts

set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandBanksCosts
open Scales TrimScales StageBounds CostLedger BandScales SubsetAddress
namespace ThreeSum.SourceBandBanksCosts
theorem _root_.solution (h J : ℕ) : LightBlockSourceRetainedHost.space 0 h J ≤
    J+2*(J*(512*h))+(J*(512*h)+1)^2+
      Nat.log 2 ((512*h)*LocalCoverBounds.localPrime h+1)+
      Nat.log 2 (LightBlockSourceBuild.endpointBound h J+1)+20 := by
  unfold LightBlockSourceRetainedHost.space LightSourcePreparation.space LightBlockSourceHashes.space
    LightSourceMaskFlags.space LightSourceRetainedStages.space LightPascal.tableSize
  omega
end ThreeSum.SourceBandBanksCosts
