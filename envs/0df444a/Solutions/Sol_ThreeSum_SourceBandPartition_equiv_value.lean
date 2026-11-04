-- Prove2me | solution 1 for ThreeSum.SourceBandPartition.equiv_value
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:54:08.789997+00:00
-- url     : https://prove2.me/submissions/3e2fe4d2-e0e9-4aee-8335-d6f5256d9331

import Definitions.Def_Submission_ThreeSum_SourceBandLayout
import Definitions.Def_Submission_ThreeSum_SourceBandPartition

set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandPartition
open BandPartition SourceBandLayout
namespace ThreeSum.SourceBandPartition
theorem _root_.solution {n g i : ℕ} (f : ℕ → ℤ) (j : Fin (len n g i)) :
    f (start g i+j.val) = f ((equiv n g i j).val.val) := rfl
end ThreeSum.SourceBandPartition
