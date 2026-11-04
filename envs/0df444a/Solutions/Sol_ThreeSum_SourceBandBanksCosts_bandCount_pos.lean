-- Prove2me | solution 1 for ThreeSum.SourceBandBanksCosts.bandCount_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:24:40.978867+00:00
-- url     : https://prove2.me/submissions/187fa084-8b09-4519-a8b6-ba6cb5f40efc

import Definitions.Def_Submission_ThreeSum_LightSourceBandBanksProgram
import Definitions.Def_Submission_ThreeSum_SourceBandPairCosts
import Definitions.Def_Submission_ThreeSum_SourceBandBanksCosts
import Theorems.Thm_ThreeSum_CostLedger_bandCount_mul_bounds


set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandBanksCosts
open Scales TrimScales StageBounds CostLedger BandScales SubsetAddress
namespace ThreeSum.SourceBandBanksCosts
theorem _root_.solution {n : ℕ} (hn : 0 < n) : 0 < bandCount n := by
  have hp := (bandCount_mul_bounds n).1
  by_contra h
  have hz : bandCount n=0 := by omega
  rw [hz,Nat.mul_zero] at hp
  omega
end ThreeSum.SourceBandBanksCosts
