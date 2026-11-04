-- Prove2me | solution 1 for ThreeSum.SourceBandBanksCosts.count_le_bandCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:24:38.549871+00:00
-- url     : https://prove2.me/submissions/4d3e93f8-9267-41e8-ac9f-09ccd14bc446

import Definitions.Def_Submission_ThreeSum_LightSourceBandBanksProgram
import Definitions.Def_Submission_ThreeSum_SourceBandPairCosts
import Definitions.Def_Submission_ThreeSum_SourceBandBanksCosts
import Theorems.Thm_ThreeSum_SourceBandCosts_size_le_bandCount


set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandBanksCosts
open Scales TrimScales StageBounds CostLedger BandScales SubsetAddress
namespace ThreeSum.SourceBandBanksCosts
theorem _root_.solution {NL NR n : ℕ} (hNL : NL ≤ n) (hNR : NR ≤ n) :
    SourceBandPairSlices.count NL NR (bandSize n) ≤ bandCount n :=
  max_le (SourceBandCosts.size_le_bandCount hNL) (SourceBandCosts.size_le_bandCount hNR)
end ThreeSum.SourceBandBanksCosts
