-- Prove2me | solution 1 for ThreeSum.SourceBandBanksCosts.finish_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:31:10.71021+00:00
-- url     : https://prove2.me/submissions/e1053751-438d-46d2-b1a1-6e8b23e1cd27

import Definitions.Def_Submission_ThreeSum_LightSourceBandBanksProgram
import Definitions.Def_Submission_ThreeSum_SourceBandPairCosts
import Definitions.Def_Submission_ThreeSum_SourceBandBanksCosts

set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandBanksCosts
open Scales TrimScales StageBounds CostLedger BandScales SubsetAddress
namespace ThreeSum.SourceBandBanksCosts
theorem _root_.solution (base NL NR g h J cut : ℕ) :
    SourceBandBankData.finish base NL NR g h J cut=
      base+5+SourceBandPairSlices.count NL NR g*SourceBandBankLayout.span h J cut := rfl
end ThreeSum.SourceBandBanksCosts
