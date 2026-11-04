-- Prove2me | solution 1 for ThreeSum.SourceBandBanksCosts.familyCount_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:36:06.939565+00:00
-- url     : https://prove2.me/submissions/ddd2ebb8-4e51-40dd-bc04-b958e3a18575

import Definitions.Def_Submission_ThreeSum_LightSourceBandBanksProgram
import Definitions.Def_Submission_ThreeSum_SourceBandPairCosts
import Definitions.Def_Submission_ThreeSum_SourceBandBanksCosts
import Theorems.Thm_ThreeSum_SourceBandBanksCosts_count_le_bandCount
import Theorems.Thm_ThreeSum_BlockSourceCatalogCosts_count_eq_scheduleCount


set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandBanksCosts
open Scales TrimScales StageBounds CostLedger BandScales SubsetAddress
namespace ThreeSum.SourceBandBanksCosts
theorem _root_.solution {NL NR n : ℕ} (hNL : NL ≤ n) (hNR : NR ≤ n) :
    familyCount NL NR (bandSize n) (microHalf (inputBits n)) (blockCount (inputBits n)) ≤
      2*bandCount n*scheduleCount n := by
  unfold familyCount
  rw [BlockSourceCatalogCosts.count_eq_scheduleCount]
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 (count_le_bandCount hNL hNR))
end ThreeSum.SourceBandBanksCosts
