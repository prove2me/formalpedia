-- Prove2me | solution 1 for ThreeSum.SourceControlLayout.scratch_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:33:26.907199+00:00
-- url     : https://prove2.me/submissions/575b4ae1-681a-4583-a6e7-90043af8350b

import Definitions.Def_Submission_ThreeSum_SourceBandBanksCosts
import Definitions.Def_Submission_ThreeSum_SourceControlLayout

set_option autoImplicit false
open ThreeSum ThreeSum.SourceControlLayout
open GlobalEncoding LocalCoverBounds BlockSourceEncoding SubsetAddress
namespace ThreeSum.SourceControlLayout
theorem _root_.solution (h J : ℕ) :
    scratch J (J*(512*h)) (Nat.log 2 ((512*h)*localPrime h+1))
      (Nat.log 2 (LightBlockSourceBuild.endpointBound h J+1)) =
      LightBlockSourceRetainedHost.space 0 h J := by
  unfold scratch LightBlockSourceRetainedHost.space LightSourcePreparation.space
    LightBlockSourceHashes.space LightSourceMaskFlags.space LightSourceRetainedStages.space
    LightPascal.tableSize
  omega
end ThreeSum.SourceControlLayout
