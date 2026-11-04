-- Prove2me | solution 1 for ThreeSum.MaskDifference.subsetMask_sdiff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:48:57.067199+00:00
-- url     : https://prove2.me/submissions/b4821931-2f33-4977-8b7e-f680491bbc29

import Definitions.Def_Submission_ThreeSum_SubsetAddress
import Definitions.Def_Submission_ThreeSum_MaskDifference
import Definitions.Def_WeightedCache3SUM_Alias_6d7afa1ff9c32588

set_option autoImplicit false
open ThreeSum ThreeSum.MaskDifference
open Finset ThreeSum.SubsetAddress
namespace ThreeSum.MaskDifference
theorem _root_.solution {L : ℕ} (Q U : Finset (Fin L)) (hU : U ⊆ Q) :
    subsetMask Q-subsetMask U = subsetMask (Q \ U) := by
  have h := subsetMask_union_sdiff Q U hU
  omega
end ThreeSum.MaskDifference
