-- Prove2me | solution 1 for ThreeSum.SourceFiniteCosts.space_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:08:34.515349+00:00
-- url     : https://prove2.me/submissions/02d77e7b-4337-4f83-ab36-f069e527c462

import Definitions.Def_Submission_ThreeSum_SourceControlCosts
import Definitions.Def_Submission_ThreeSum_SourceFiniteCosts
import Theorems.Thm_ThreeSum_SourceBandBanksCosts_space_le_encoderCount
import Definitions.Def_WeightedCache3SUM_Alias_efe4583c1ba8c927
import Definitions.Def_WeightedCache3SUM_Alias_e585c8aa48ae4f7c


set_option autoImplicit false
open ThreeSum ThreeSum.SourceFiniteCosts
open Scales TrimScales StageBounds CostLedger BandScales
namespace ThreeSum.SourceFiniteCosts
theorem _root_.solution {base NL NR n p U D : ℕ} (hn : 0 < n) (hNL : NL ≤ n) (hNR : NR ≤ n) :
    LightSourceControlsHost.space base NL NR (bandSize n) p
      (microHalf (inputBits n)) (blockCount (inputBits n)) (mu n) U D ≤ space base n p U D :=
  SourceControlCosts.space_le_encoderCount hn hNL hNR
end ThreeSum.SourceFiniteCosts
