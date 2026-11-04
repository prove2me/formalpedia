-- Prove2me | solution 1 for ThreeSum.BandRawA.count_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:38:23.454554+00:00
-- url     : https://prove2.me/submissions/b44e4747-abcf-490a-9ced-dab011d5a50c

import Definitions.Def_Submission_ThreeSum_BandCandidateRowsMemory
import Definitions.Def_Submission_ThreeSum_BandPartition
import Definitions.Def_Submission_ThreeSum_BandRawA
import Theorems.Thm_ThreeSum_BandRawA_count_succ

set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows BandEnumeration BandPartition
set_option maxHeartbeats 1600000
set_option maxRecDepth 7000
namespace ThreeSum.BandRawA
theorem _root_.solution (n g : ℕ) (rs : List Record) : Monotone (count n g rs) := by
  apply monotone_nat_of_le_succ
  intro i
  rw [count_succ]
  omega
end ThreeSum.BandRawA
