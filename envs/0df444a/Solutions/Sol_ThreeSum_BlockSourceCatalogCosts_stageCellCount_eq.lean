-- Prove2me | solution 1 for ThreeSum.BlockSourceCatalogCosts.stageCellCount_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:11:19.537196+00:00
-- url     : https://prove2.me/submissions/33c73239-5641-4a79-a3ad-053204f598c1

import Definitions.Def_Submission_ThreeSum_LightBlockSourceCatalogProgram
import Definitions.Def_Submission_ThreeSum_BlockSourceStageCosts
import Definitions.Def_Submission_ThreeSum_BlockSourceCatalogCosts
import Theorems.Thm_ThreeSum_BlockSourceCatalogCosts_stageFamilyCount_eq

set_option autoImplicit false
open ThreeSum ThreeSum.BlockSourceCatalogCosts
open Scales TrimScales StageBounds CostLedger BlockSourceSharing SubsetAddress
open LightBlockSourceBatchLayout
namespace ThreeSum.BlockSourceCatalogCosts
theorem _root_.solution (n : ℕ) :
    stageCellCount n = 2*bandCount n*scheduleCount n*(256*mu n+1)*
      downsetCap (256*mu n) (mu n) := by
  unfold stageCellCount family
  rw [stageFamilyCount_eq]
  ring
end ThreeSum.BlockSourceCatalogCosts
