-- Prove2me | solution 1 for ThreeSum.BlockSourceFlags.right_product
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:06:19.2042+00:00
-- url     : https://prove2.me/submissions/ef9b1061-2e7b-4726-8f9a-4785380b1c00

import Definitions.Def_Submission_ThreeSum_BlockSourceRows
import Definitions.Def_Submission_ThreeSum_LightSourceTrim
import Definitions.Def_Submission_ThreeSum_LightLocalCoverSchedule
import Definitions.Def_Submission_ThreeSum_BlockSourceFlags
import Theorems.Thm_ThreeSum_BlockSourceFlags_right_row_iff
import Theorems.Thm_ThreeSum_LightSourceTrim_rowFlag_le
import Theorems.Thm_ThreeSum_SourceFlagProduct_product_eq_indicator


set_option autoImplicit false
open ThreeSum ThreeSum.BlockSourceFlags
open BlockRows BlockIndex BlockEncoding BlockCoefficientRows
open LocalHashMoments LocalCoverBounds GlobalEncoding
set_option maxHeartbeats 1200000
namespace ThreeSum.BlockSourceFlags
theorem _root_.solution {h J : ℕ} (o : Occurrences h J) (S : Finset (Coord J (512*h))) :
    SourceFlagProduct.product
      (LightSourceTrim.rowFlag (512*h) h (localPrime h) (localBucketCap h)
        (occurrenceIndices o) (candidateIndices h) (bits S)
        (mapRow h true) (mapRow h false) (rightCount h)) J =
      if RightAllowed o S then 1 else 0 := by
  apply SourceFlagProduct.product_eq_indicator
  · exact fun _ _ => LightSourceTrim.rowFlag_le ..
  · constructor
    · intro hall j
      exact (right_row_iff o S j).mp (hall j.val j.isLt)
    · intro hall j hj
      exact (right_row_iff o S ⟨j,hj⟩).mpr (hall ⟨j,hj⟩)
end ThreeSum.BlockSourceFlags
