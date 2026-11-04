-- Prove2me | solution 1 for ThreeSum.SourceBandCosts.modulus_le_tableCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:28:00.027095+00:00
-- url     : https://prove2.me/submissions/7f2ed721-cf5a-4462-b2df-6845c6e79eba

import Definitions.Def_Submission_ThreeSum_LightSourceBandSetup
import Definitions.Def_Submission_ThreeSum_BlockSourceCatalogCosts
import Mathlib.Data.Nat.Choose.Vandermonde
import Definitions.Def_Submission_ThreeSum_SourceBandCosts
import Theorems.Thm_ThreeSum_SourceBandCosts_modulus_le_global_outputs
import Theorems.Thm_ThreeSum_BlockSourceCatalogCosts_count_eq_scheduleCount
import Theorems.Thm_ThreeSum_BlockSourceSharing_cutoff_eq
import Theorems.Thm_ThreeSum_BlockSourceSharing_width_eq


set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandCosts
open Scales TrimScales StageBounds CostLedger BandScales LocalCoverBounds
namespace ThreeSum.SourceBandCosts
theorem _root_.solution (n : ℕ) :
    BlockSourceEncoding.modulus (microHalf (inputBits n)) (blockCount (inputBits n)) ≤ tableCount n := by
  have hm := modulus_le_global_outputs (microHalf (inputBits n)) (blockCount (inputBits n))
  have hc : blockCount (inputBits n)*(2*microHalf (inputBits n))=mu n := by
    rw [Nat.mul_comm,BlockSourceSharing.cutoff_eq]
  rw [BlockSourceSharing.width_eq,hc] at hm
  change LightBlockSourceCatalog.count (microHalf (inputBits n)) (blockCount (inputBits n))*fullOutputs n ≥ _ at hm
  rw [BlockSourceCatalogCosts.count_eq_scheduleCount] at hm
  exact hm
end ThreeSum.SourceBandCosts
