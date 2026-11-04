-- Prove2me | solution 1 for ThreeSum.BlockSourceFlags.left_product
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:05:59.311249+00:00
-- url     : https://prove2.me/submissions/a450f8ac-1fcb-45a9-8347-98cb38670cc2

import Definitions.Def_Submission_ThreeSum_BlockSourceRows
import Definitions.Def_Submission_ThreeSum_LightSourceTrim
import Definitions.Def_Submission_ThreeSum_LightLocalCoverSchedule
import Definitions.Def_Submission_ThreeSum_BlockSourceFlags
import Theorems.Thm_ThreeSum_BlockSourceFlags_left_row_iff
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
        (mapRow h false) (mapRow h true) (leftCount h)) J =
      if LeftAllowed o S then 1 else 0 := by
  apply SourceFlagProduct.product_eq_indicator
  · exact fun _ _ => LightSourceTrim.rowFlag_le ..
  · constructor
    · intro hall j
      exact (left_row_iff o S j).mp (hall j.val j.isLt)
    · intro hall j hj
      exact (left_row_iff o S ⟨j,hj⟩).mpr (hall ⟨j,hj⟩)
end ThreeSum.BlockSourceFlags
