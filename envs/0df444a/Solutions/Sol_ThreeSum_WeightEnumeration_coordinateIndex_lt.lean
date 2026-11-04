-- Prove2me | solution 1 for ThreeSum.WeightEnumeration.coordinateIndex_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:47:06.972194+00:00
-- url     : https://prove2.me/submissions/c089c314-1112-49d6-b069-bd5881bef52f

import Definitions.Def_Submission_ThreeSum_LocalHashMoments
import Mathlib.Data.List.Range
import Definitions.Def_Submission_ThreeSum_WeightEnumeration

set_option autoImplicit false
open ThreeSum ThreeSum.WeightEnumeration
open LocalHashMoments
variable {ι K : Type*} [DecidableEq ι] [NatCast K]
namespace ThreeSum.WeightEnumeration
theorem _root_.solution {L : ℕ} (i : Fin L × Bool) : coordinateIndex i < 2*L := by
  have hi := i.1.isLt
  unfold coordinateIndex
  split <;> omega
end ThreeSum.WeightEnumeration
