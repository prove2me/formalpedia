-- Prove2me | solution 1 for ThreeSum.MaskDifference.subsetMask_sdiff_int
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:51:34.94529+00:00
-- url     : https://prove2.me/submissions/aeacd253-e6bb-495d-a03c-a7aeac62af6f

import Definitions.Def_Submission_ThreeSum_SubsetAddress
import Definitions.Def_Submission_ThreeSum_MaskDifference
import Definitions.Def_WeightedCache3SUM_Alias_6d7afa1ff9c32588

set_option autoImplicit false
open ThreeSum ThreeSum.MaskDifference
open Finset ThreeSum.SubsetAddress
namespace ThreeSum.MaskDifference
theorem _root_.solution {L : ℕ} (Q U : Finset (Fin L)) (hU : U ⊆ Q) :
    (subsetMask Q : ℤ)-(subsetMask U : ℤ) = (subsetMask (Q \ U) : ℤ) := by
  have h := subsetMask_union_sdiff Q U hU
  have hz : (subsetMask U : ℤ)+(subsetMask (Q \ U) : ℤ) = (subsetMask Q : ℤ) := by
    exact_mod_cast h
  omega
end ThreeSum.MaskDifference
