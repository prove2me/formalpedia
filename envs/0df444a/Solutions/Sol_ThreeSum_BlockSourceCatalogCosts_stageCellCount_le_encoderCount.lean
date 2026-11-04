-- Prove2me | solution 1 for ThreeSum.BlockSourceCatalogCosts.stageCellCount_le_encoderCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:17:57.541317+00:00
-- url     : https://prove2.me/submissions/3e26b028-8cb8-4cb3-a794-c4f6c0266fdb

import Definitions.Def_Submission_ThreeSum_LightBlockSourceCatalogProgram
import Definitions.Def_Submission_ThreeSum_BlockSourceStageCosts
import Definitions.Def_Submission_ThreeSum_BlockSourceCatalogCosts
import Theorems.Thm_ThreeSum_BlockSourceCatalogCosts_stageCellCount_eq
import Theorems.Thm_ThreeSum_BlockSourceSharing_downset_le_fullOutputs


set_option autoImplicit false
open ThreeSum ThreeSum.BlockSourceCatalogCosts
open Scales TrimScales StageBounds CostLedger BlockSourceSharing SubsetAddress
open LightBlockSourceBatchLayout
namespace ThreeSum.BlockSourceCatalogCosts
theorem _root_.solution (n : ℕ) :
    stageCellCount n ≤ (256*mu n+1)*(mu n+1)*encoderCount n := by
  rw [stageCellCount_eq]
  calc
    _ ≤ 2*bandCount n*scheduleCount n*(256*mu n+1)*((mu n+1)*fullOutputs n) :=
      Nat.mul_le_mul_left _ (downset_le_fullOutputs n)
    _ = _ := by unfold encoderCount; ring
end ThreeSum.BlockSourceCatalogCosts
