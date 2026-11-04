-- Prove2me | solution 1 for ThreeSum.SharedReportingBankResourceBounds.index_word_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:19:14.187064+00:00
-- url     : https://prove2.me/submissions/72fa9b87-838c-4126-8631-cf7c0c4e13a8

import Definitions.Def_Submission_ThreeSum_SharedReportingBankCosts
import Definitions.Def_Submission_ThreeSum_PolynomialResources
import Definitions.Def_Submission_ThreeSum_SharedReportingBankResourceBounds

set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingBankResourceBounds
open Light SubsetAddress SharedReportingBankLayout SharedReportingBankLevels
open SharedReportingBankHeader SharedReportingBankRows
set_option maxHeartbeats 2800000
set_option maxRecDepth 14000
namespace ThreeSum.SharedReportingBankResourceBounds
theorem _root_.solution {W a b : ℕ} (hab : a ≤ b) :
    LightReportingSortedCatalog.word W a ≤ LightReportingSortedCatalog.word W b := by
  have hm := Nat.mul_le_mul_left ((2^W)^2) (Nat.add_le_add_right hab 1)
  unfold LightReportingSortedCatalog.word LightReportingPackKeys.word
  omega
end ThreeSum.SharedReportingBankResourceBounds
