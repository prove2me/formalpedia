-- Prove2me | solution 1 for ThreeSum.SourceBandHostCosts.time_le_encoderCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:28:48.691922+00:00
-- url     : https://prove2.me/submissions/cc375894-9553-485e-b654-c412bbf028d1

import Definitions.Def_Submission_ThreeSum_LightSourceBandHostProgram
import Definitions.Def_Submission_ThreeSum_SourceBandBanksCosts
import Definitions.Def_Submission_ThreeSum_SourceBandHostCosts
import Definitions.Def_WeightedCache3SUM_Alias_1a074e2b77e127b6
import Definitions.Def_WeightedCache3SUM_Alias_8b3592271bea283a
import Theorems.Thm_ThreeSum_SourceBandPairCosts_time_le_encoderCount


set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandHostCosts
open Scales TrimScales StageBounds CostLedger BandScales
namespace ThreeSum.SourceBandHostCosts
theorem _root_.solution {NL NR n p U D : ℕ} (hn : 0 < n) (hNL : NL ≤ n) (hNR : NR ≤ n) :
    LightSourceBandHost.time NL NR (bandSize n) p
      (microHalf (inputBits n)) (blockCount (inputBits n)) (mu n) U D ≤
      (LightBlockSourceCatalogProgram.factor (microHalf (inputBits n)) (blockCount (inputBits n))*(256*mu n+2)+
        2032*(Nat.log 2 (U+1)+Nat.log 2 (p+D+1)+1)+5205)*encoderCount n+4859 := by
  have hp := SourceBandPairCosts.time_le_encoderCount (p := p) (U := U) (D := D) hn hNL hNR
  have hb := SourceBandBanksCosts.time_le_encoderCount hn hNL hNR
  unfold LightSourceBandHost.time
  nlinarith
end ThreeSum.SourceBandHostCosts
