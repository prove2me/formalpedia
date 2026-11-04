-- Prove2me | solution 1 for ThreeSum.SharedReportingBankSources.source_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:20:12.063769+00:00
-- url     : https://prove2.me/submissions/20153673-6f94-4d40-ae8e-abdea124ff7c

import Definitions.Def_Submission_ThreeSum_SharedReportingBankSources
import Definitions.Def_Submission_ThreeSum_SourceBandFinite
import Definitions.Def_Submission_ThreeSum_SharedReportingBankSourceBounds
import Theorems.Thm_ThreeSum_BandPartition_length_le
import Theorems.Thm_ThreeSum_BandWeightedScore_length_le
import Theorems.Thm_ThreeSum_SourceBandPartition_source_card


set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingBankSources
open Light SubsetAddress BlockIndexedQuery GlobalEncoding
namespace ThreeSum.SharedReportingBankSources
theorem _root_.solution (n g i : ℕ) : (SourceBandPartition.source n g i).card ≤ g := by
  rw [SourceBandPartition.source_card]
  exact BandPartition.length_le n g i
end ThreeSum.SharedReportingBankSources
