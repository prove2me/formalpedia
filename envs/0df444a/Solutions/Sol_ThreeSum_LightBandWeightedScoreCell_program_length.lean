-- Prove2me | solution 1 for ThreeSum.LightBandWeightedScoreCell.program_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:28:07.159199+00:00
-- url     : https://prove2.me/submissions/34f1af86-366b-49f6-b799-f51d15fa4091

import Definitions.Def_Submission_ThreeSum_LightBandWeightedScoreSlice
import Definitions.Def_Submission_ThreeSum_BandCandidateRowsMemory
import Definitions.Def_Submission_ThreeSum_ReportingHostRelocation
import Definitions.Def_Submission_ThreeSum_LightBandWeightedScoreCell

set_option autoImplicit false
open ThreeSum ThreeSum.LightBandWeightedScoreCell
open Light BandCandidateRows BandWeightedScore
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ}
    {a b c nA nB nC g rec q aux s free maxMod U : ℕ}
namespace ThreeSum.LightBandWeightedScoreCell
theorem _root_.solution : program.length=16 := rfl
end ThreeSum.LightBandWeightedScoreCell
