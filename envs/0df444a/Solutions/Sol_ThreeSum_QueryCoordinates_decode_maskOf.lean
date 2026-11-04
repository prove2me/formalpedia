-- Prove2me | solution 1 for ThreeSum.QueryCoordinates.decode_maskOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:05:40.80139+00:00
-- url     : https://prove2.me/submissions/002081db-331f-4a2b-9146-6d898d41c0d4

import Definitions.Def_Submission_ThreeSum_LightWeightedEnumeration
import Definitions.Def_Submission_ThreeSum_MaskDifference
import Definitions.Def_Submission_ThreeSum_MaskDecode
import Mathlib.Data.List.Sublists
import Mathlib.Algebra.BigOperators.Fin
import Definitions.Def_Submission_ThreeSum_QueryCoordinates
import Theorems.Thm_ThreeSum_MaskDecode_subsetMask_decode
import Theorems.Thm_ThreeSum_SubsetAddress_maskOf_injective
import Theorems.Thm_ThreeSum_SubsetAddress_maskOf_isMask


set_option autoImplicit false
open ThreeSum ThreeSum.QueryCoordinates
open Finset ThreeSum.SubsetAddress
open scoped BigOperators
namespace ThreeSum.QueryCoordinates
theorem _root_.solution {W : ℕ} {s : Finset ℕ} (hs : s ⊆ range W) :
    natPositions (MaskDecode.decode W (maskOf s)) = s := by
  apply maskOf_injective
  exact MaskDecode.subsetMask_decode (maskOf_isMask hs).1
end ThreeSum.QueryCoordinates
