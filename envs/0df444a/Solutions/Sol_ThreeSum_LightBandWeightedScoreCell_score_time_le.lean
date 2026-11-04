-- Prove2me | solution 1 for ThreeSum.LightBandWeightedScoreCell.score_time_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:59:41.250206+00:00
-- url     : https://prove2.me/submissions/dd8590be-2088-4ade-a1b1-e2d0f6374b1e

import Definitions.Def_Submission_ThreeSum_LightBandWeightedScoreSlice
import Definitions.Def_Submission_ThreeSum_BandCandidateRowsMemory
import Definitions.Def_Submission_ThreeSum_ReportingHostRelocation
import Definitions.Def_Submission_ThreeSum_LightBandWeightedScoreCell

set_option autoImplicit false
open ThreeSum ThreeSum.LightBandWeightedScoreCell
open Light BandCandidateRows BandWeightedScore
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
namespace ThreeSum.LightBandWeightedScoreCell
theorem _root_.solution {nA nB nC g : ℕ} (maxMod s U : ℕ)
    (hA : nA ≤ g) (hB : nB ≤ g) (hC : nC ≤ g) :
    LightWeightedScore.runtimeTime maxMod nA nB nC s U ≤
      LightWeightedScore.runtimeTime maxMod g g g s U := by
  have hta := Nat.mul_le_mul_right (LightResidues.residueBudget U+30) hA
  have htb := Nat.mul_le_mul_right (LightResidues.residueBudget U+30) hB
  have htc := Nat.mul_le_mul_right (LightResidues.residueBudget U+30) hC
  have hc : LightModuloCounts.time maxMod nA nB nC U ≤ LightModuloCounts.time maxMod g g g U := by
    unfold LightModuloCounts.time LightResidueHistogram.time LightHistogram.histogramTime
      LightHistogram.countTime LightResidues.residuesTime LightLookupSum.time
    omega
  have hs := Nat.mul_le_mul_left s (Nat.add_le_add_right
    (Nat.add_le_add_right hc (LightWeightedScore.jointTime maxMod)) 100)
  unfold LightWeightedScore.runtimeTime LightWeightedScore.time
  omega
end ThreeSum.LightBandWeightedScoreCell
