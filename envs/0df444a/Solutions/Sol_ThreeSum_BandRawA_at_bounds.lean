-- Prove2me | solution 1 for ThreeSum.BandRawA.at_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:05:46.903225+00:00
-- url     : https://prove2.me/submissions/9c8693f9-f896-42b1-8f0d-9b2bef90f93c

import Definitions.Def_Submission_ThreeSum_BandRawAMemory
import Definitions.Def_Submission_ThreeSum_BandRawAIndex
import Theorems.Thm_ThreeSum_BandRawA_at_mem
import Theorems.Thm_ThreeSum_BandRawA_mem_firstRows
import Definitions.Def_WeightedCache3SUM_Alias_c1d8c5e2c3bbb05a
import Theorems.Thm_ThreeSum_BlockRows_mem_row
attribute [local simp] ThreeSum.BlockRows.mem_row



set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows
set_option maxHeartbeats 1700000
set_option maxRecDepth 7000
namespace ThreeSum.BandRawA
theorem _root_.solution {n g k : ℕ} {rs : List Record}
    (hk : k < (items n g rs).length) :
    (labelAt n g rs k).owner < rs.length ∧
      (ownerRecord n g rs k).flag=1 ∧
      BandPartition.start g (ownerRecord n g rs k).a ≤ (labelAt n g rs k).position ∧
      (labelAt n g rs k).position < BandPartition.stop n g (ownerRecord n g rs k).a := by
  have hh := mem_firstRows.mp (at_mem hk)
  have hr := mem_row.mp hh.2
  exact ⟨hh.1,hr.1,hr.2.2.1,hr.2.2.2⟩
end ThreeSum.BandRawA
