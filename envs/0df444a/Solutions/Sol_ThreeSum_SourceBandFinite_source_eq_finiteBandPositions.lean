-- Prove2me | solution 1 for ThreeSum.SourceBandFinite.source_eq_finiteBandPositions
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:12:49.023206+00:00
-- url     : https://prove2.me/submissions/5f559c7b-f321-4f5a-b779-c5a5fa6afcb4

import Definitions.Def_Submission_ThreeSum_SourceBandBankData
import Definitions.Def_Submission_ThreeSum_BandRawAFiniteSlices
import Definitions.Def_Submission_ThreeSum_SourceBandFinite
import Theorems.Thm_ThreeSum_BandRawA_mem_bandPositions
import Theorems.Thm_ThreeSum_BandRawA_mem_finiteBandPositions
attribute [local simp] ThreeSum.BandRawA.mem_finiteBandPositions



set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandFinite
open GlobalEncoding OutputDecodeRecords
namespace ThreeSum.SourceBandFinite
theorem _root_.solution (n g i : ℕ) :
    SourceBandPartition.source n g i=BandRawA.finiteBandPositions n g i := by
  ext t
  rw [SourceBandPartition.mem_source,BandRawA.mem_finiteBandPositions,BandRawA.mem_bandPositions]
end ThreeSum.SourceBandFinite
