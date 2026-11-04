-- Prove2me | solution 1 for ThreeSum.SourceBandHostCosts.scheduleCount_le_encoderCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:41:33.67695+00:00
-- url     : https://prove2.me/submissions/ead17bd4-a1aa-425d-ba17-b9e30483ecc6

import Definitions.Def_Submission_ThreeSum_LightSourceBandHostProgram
import Definitions.Def_Submission_ThreeSum_SourceBandBanksCosts
import Definitions.Def_Submission_ThreeSum_SourceBandHostCosts
import Theorems.Thm_ThreeSum_BandScales_typedOutputs_pos
import Theorems.Thm_ThreeSum_SourceBandCosts_typedOutputs_le_fullOutputs
import Theorems.Thm_ThreeSum_SourceBandPairCosts_tableCount_le_encoderCount


set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandHostCosts
open Scales TrimScales StageBounds CostLedger BandScales
namespace ThreeSum.SourceBandHostCosts
theorem _root_.solution {n : ℕ} (hn : 0 < n) : scheduleCount n ≤ encoderCount n := by
  have hf : 0 < fullOutputs n :=
    (typedOutputs_pos n).trans_le (SourceBandCosts.typedOutputs_le_fullOutputs n)
  have hs : scheduleCount n ≤ tableCount n := Nat.le_mul_of_pos_right _ hf
  exact hs.trans (SourceBandPairCosts.tableCount_le_encoderCount hn)
end ThreeSum.SourceBandHostCosts
