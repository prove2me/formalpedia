-- Prove2me | solution 1 for ThreeSum.SourceBandBanksCosts.stageCells_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:26:00.149446+00:00
-- url     : https://prove2.me/submissions/427b42aa-87ad-49a9-bfaf-4c04d89aecda

import Definitions.Def_Submission_ThreeSum_LightSourceBandBanksProgram
import Definitions.Def_Submission_ThreeSum_SourceBandPairCosts
import Definitions.Def_Submission_ThreeSum_SourceBandBanksCosts

set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandBanksCosts
open Scales TrimScales StageBounds CostLedger BandScales SubsetAddress
namespace ThreeSum.SourceBandBanksCosts
theorem _root_.solution (NL NR g h J cut : ℕ) :
    stageCells NL NR g h J cut=
      2*SourceBandPairSlices.count NL NR g*LightBlockSourceCatalog.count h J*
        (J*(512*h)+1)*downsetCap (J*(512*h)) cut := by
  unfold stageCells familyCount LightBlockSourceBatchLayout.family
  ring
end ThreeSum.SourceBandBanksCosts
