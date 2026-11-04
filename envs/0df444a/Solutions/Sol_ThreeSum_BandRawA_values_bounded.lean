-- Prove2me | solution 1 for ThreeSum.BandRawA.values_bounded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:11:38.809619+00:00
-- url     : https://prove2.me/submissions/110bf1c8-c120-4a3d-b9b3-741d8c7ac9d7

import Definitions.Def_Submission_ThreeSum_BandCandidateRowsMemory
import Definitions.Def_Submission_ThreeSum_BandPartition
import Definitions.Def_Submission_ThreeSum_BandRawA
import Theorems.Thm_ThreeSum_BandRawA_position_lt

set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows BandEnumeration BandPartition
set_option maxHeartbeats 1600000
set_option maxRecDepth 7000
namespace ThreeSum.BandRawA
theorem _root_.solution {n g i U : ℕ} {rs : List Record} {f : ℕ → ℤ}
    (hf : ∀ j < n, |f j| ≤ (U : ℤ)) :
    ∀ v ∈ values f (firstRows n g rs i), |v| ≤ (U : ℤ) := by
  intro v hv
  obtain ⟨l,hl,rfl⟩ := List.mem_map.mp hv
  exact hf l.position (position_lt hl)
end ThreeSum.BandRawA
