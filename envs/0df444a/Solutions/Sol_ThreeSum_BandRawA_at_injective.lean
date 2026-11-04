-- Prove2me | solution 1 for ThreeSum.BandRawA.at_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:52:10.715696+00:00
-- url     : https://prove2.me/submissions/b72c4cf9-7415-4a9f-a59a-897437dd2d76

import Definitions.Def_Submission_ThreeSum_BandRawAMemory
import Definitions.Def_Submission_ThreeSum_BandRawAIndex
import Theorems.Thm_ThreeSum_BandRawA_index_eq_owner_local

set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows
set_option maxHeartbeats 1700000
set_option maxRecDepth 7000
namespace ThreeSum.BandRawA
theorem _root_.solution {n g : ℕ} {rs : List Record} {i j : ℕ}
    (hi : i < (items n g rs).length) (hj : j < (items n g rs).length)
    (he : labelAt n g rs i=labelAt n g rs j) : i=j := by
  have hi' := index_eq_owner_local hi
  have hj' := index_eq_owner_local hj
  rw [localA,ownerRecord,he] at hi'
  rw [localA,ownerRecord] at hj'
  omega
end ThreeSum.BandRawA
