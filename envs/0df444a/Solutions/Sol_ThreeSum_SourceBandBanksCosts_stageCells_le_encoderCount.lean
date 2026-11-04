-- Prove2me | solution 1 for ThreeSum.SourceBandBanksCosts.stageCells_le_encoderCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:41:56.794206+00:00
-- url     : https://prove2.me/submissions/65212e60-83b0-42b2-aec4-cf1ebdbf19c9

import Definitions.Def_Submission_ThreeSum_LightSourceBandBanksProgram
import Definitions.Def_Submission_ThreeSum_SourceBandPairCosts
import Definitions.Def_Submission_ThreeSum_SourceBandBanksCosts
import Theorems.Thm_ThreeSum_SourceBandBanksCosts_familyCount_le
import Theorems.Thm_ThreeSum_BlockSourceCatalogCosts_stageCellCount_le_encoderCount
import Theorems.Thm_ThreeSum_BlockSourceCatalogCosts_stageFamilyCount_eq
import Theorems.Thm_ThreeSum_BlockSourceSharing_width_eq


set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandBanksCosts
open Scales TrimScales StageBounds CostLedger BandScales SubsetAddress
namespace ThreeSum.SourceBandBanksCosts
theorem _root_.solution {NL NR n : ℕ} (hNL : NL ≤ n) (hNR : NR ≤ n) :
    stageCells NL NR (bandSize n) (microHalf (inputBits n)) (blockCount (inputBits n)) (mu n) ≤
      (256*mu n+1)*(mu n+1)*encoderCount n := by
  have hf := familyCount_le hNL hNR
  unfold stageCells
  rw [BlockSourceSharing.width_eq]
  have hm := Nat.mul_le_mul_right (LightBlockSourceBatchLayout.family (256*mu n) (mu n)) hf
  have he : 2*bandCount n*scheduleCount n*LightBlockSourceBatchLayout.family (256*mu n) (mu n)=
      BlockSourceCatalogCosts.stageCellCount n := by
    unfold BlockSourceCatalogCosts.stageCellCount
    rw [BlockSourceCatalogCosts.stageFamilyCount_eq]
  exact (hm.trans_eq he).trans (BlockSourceCatalogCosts.stageCellCount_le_encoderCount n)
end ThreeSum.SourceBandBanksCosts
