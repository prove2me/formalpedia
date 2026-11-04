-- Prove2me | solution 1 for ThreeSum.BandRawA.items_length_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:52:04.792564+00:00
-- url     : https://prove2.me/submissions/8dfebbdb-5197-477b-879b-3c67e7d996ab

import Definitions.Def_Submission_ThreeSum_BandCandidateRowsMemory
import Definitions.Def_Submission_ThreeSum_BandPartition
import Definitions.Def_Submission_ThreeSum_BandRawA
import Theorems.Thm_ThreeSum_BandRawA_count_bound
import Theorems.Thm_ThreeSum_BandCandidateRows_count_bound


set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows BandEnumeration BandPartition
set_option maxHeartbeats 1600000
set_option maxRecDepth 7000
namespace ThreeSum.BandRawA
theorem _root_.solution (n g : ℕ) (rs : List Record) : (items n g rs).length ≤ g*rs.length :=
  count_bound n g rs rs.length
end ThreeSum.BandRawA
