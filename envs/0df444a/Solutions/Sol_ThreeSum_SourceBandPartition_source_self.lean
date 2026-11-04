-- Prove2me | solution 1 for ThreeSum.SourceBandPartition.source_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:54:11.242427+00:00
-- url     : https://prove2.me/submissions/5aa83b95-ea24-4299-9a30-65aec73e48c0

import Definitions.Def_Submission_ThreeSum_SourceBandLayout
import Definitions.Def_Submission_ThreeSum_SourceBandPartition
import Theorems.Thm_ThreeSum_BandPartition_index_bounds


set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandPartition
open BandPartition SourceBandLayout
namespace ThreeSum.SourceBandPartition
theorem _root_.solution {n g : ℕ} (hg : 0 < g) (t : Fin n) : t ∈ source n g (t.val/g) :=
  mem_source.mpr (index_bounds hg t.isLt)
end ThreeSum.SourceBandPartition
