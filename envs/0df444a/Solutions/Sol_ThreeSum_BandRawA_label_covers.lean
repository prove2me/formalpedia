-- Prove2me | solution 1 for ThreeSum.BandRawA.label_covers
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:05:49.27627+00:00
-- url     : https://prove2.me/submissions/e75084f7-9240-4d8c-8d35-64aebaf41e7d

import Definitions.Def_Submission_ThreeSum_BandCandidateRowsMemory
import Definitions.Def_Submission_ThreeSum_BandPartition
import Definitions.Def_Submission_ThreeSum_BandRawA
import Definitions.Def_WeightedCache3SUM_Alias_c1d8c5e2c3bbb05a
import Theorems.Thm_ThreeSum_BandRawA_mem_firstRows
import Theorems.Thm_ThreeSum_BlockRows_mem_row
attribute [local simp] ThreeSum.BlockRows.mem_row



set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows BandEnumeration BandPartition
set_option maxHeartbeats 1600000
set_option maxRecDepth 7000
namespace ThreeSum.BandRawA
theorem _root_.solution {n g s p : ℕ} {rs : List Record}
    (hs : s < rs.length) (hf : (rs.getD s default).flag=1)
    (hp : start g (rs.getD s default).a ≤ p)
    (he : p < stop n g (rs.getD s default).a) :
    (⟨s,p⟩ : Label) ∈ items n g rs :=
  mem_firstRows.mpr ⟨hs,mem_row.mpr ⟨hf,rfl,hp,he⟩⟩
end ThreeSum.BandRawA
