-- Prove2me | solution 1 for ThreeSum.SourceBandBanksCosts.finish_le_encoderCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:57:31.4582+00:00
-- url     : https://prove2.me/submissions/16b56324-f07b-4564-a364-ae01fe9f1e56

import Definitions.Def_Submission_ThreeSum_LightSourceBandBanksProgram
import Definitions.Def_Submission_ThreeSum_SourceBandPairCosts
import Definitions.Def_Submission_ThreeSum_SourceBandBanksCosts
import Theorems.Thm_ThreeSum_SourceBandBanksCosts_count_le_bandCount
import Theorems.Thm_ThreeSum_SourceBandBanksCosts_finish_eq
import Definitions.Def_WeightedCache3SUM_Alias_88da9dea387e075d

set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandBanksCosts
open Scales TrimScales StageBounds CostLedger BandScales SubsetAddress
namespace ThreeSum.SourceBandBanksCosts
theorem _root_.solution {base NL NR n : ℕ} (hNL : NL ≤ n) (hNR : NR ≤ n) :
    SourceBandBankData.finish base NL NR (bandSize n) (microHalf (inputBits n)) (blockCount (inputBits n)) (mu n) ≤
      base+5+storageFactor n*encoderCount n := by
  rw [finish_eq]
  exact Nat.add_le_add_left (span_count_le_encoderCount (count_le_bandCount hNL hNR)) _
end ThreeSum.SourceBandBanksCosts
