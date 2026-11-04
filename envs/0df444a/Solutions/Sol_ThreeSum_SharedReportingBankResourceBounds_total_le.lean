-- Prove2me | solution 1 for ThreeSum.SharedReportingBankResourceBounds.total_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:28:15.425912+00:00
-- url     : https://prove2.me/submissions/46721548-1bb5-49cd-896f-c85740b21d7d

import Definitions.Def_Submission_ThreeSum_SharedReportingBankCosts
import Definitions.Def_Submission_ThreeSum_PolynomialResources
import Definitions.Def_Submission_ThreeSum_SharedReportingBankResourceBounds
import Theorems.Thm_ThreeSum_BandPartition_size_le


set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingBankResourceBounds
open Light SubsetAddress SharedReportingBankLayout SharedReportingBankLevels
open SharedReportingBankHeader SharedReportingBankRows
set_option maxHeartbeats 2800000
set_option maxRecDepth 14000
namespace ThreeSum.SharedReportingBankResourceBounds
theorem _root_.solution {NB NC n h J g : ℕ} (hB : NB ≤ n) (hC : NC ≤ n) :
    total h J NB NC g ≤ LightBlockSourceCatalog.count h J*n*n :=
  Nat.mul_le_mul (Nat.mul_le_mul_left _ ((BandPartition.size_le NB g).trans hB))
    ((BandPartition.size_le NC g).trans hC)
end ThreeSum.SharedReportingBankResourceBounds
