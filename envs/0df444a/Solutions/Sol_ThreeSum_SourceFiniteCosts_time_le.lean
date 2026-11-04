-- Prove2me | solution 1 for ThreeSum.SourceFiniteCosts.time_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:47:54.650727+00:00
-- url     : https://prove2.me/submissions/ee07e5bd-2ea2-4c9e-ab97-199fc2ea747d

import Definitions.Def_Submission_ThreeSum_SourceControlCosts
import Definitions.Def_Submission_ThreeSum_SourceFiniteCosts
import Definitions.Def_WeightedCache3SUM_Alias_1a074e2b77e127b6
import Definitions.Def_WeightedCache3SUM_Alias_8b3592271bea283a
import Theorems.Thm_ThreeSum_SourceBandHostCosts_time_le_encoderCount
import Theorems.Thm_ThreeSum_SourceBandPairCosts_time_le_encoderCount
import Theorems.Thm_ThreeSum_SourceControlCosts_time_le_encoderCount


set_option autoImplicit false
open ThreeSum ThreeSum.SourceFiniteCosts
open Scales TrimScales StageBounds CostLedger BandScales
namespace ThreeSum.SourceFiniteCosts
theorem _root_.solution {NL NR n p U D : ℕ} (hn : 0 < n) (hNL : NL ≤ n) (hNR : NR ≤ n) :
    LightSourceControlsHost.time NL NR (bandSize n) p
      (microHalf (inputBits n)) (blockCount (inputBits n)) (mu n) U D ≤ time n p U D :=
  SourceControlCosts.time_le_encoderCount hn hNL hNR
end ThreeSum.SourceFiniteCosts
