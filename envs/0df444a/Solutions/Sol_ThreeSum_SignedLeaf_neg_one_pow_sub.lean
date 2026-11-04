-- Prove2me | solution 1 for ThreeSum.SignedLeaf.neg_one_pow_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:33:31.366592+00:00
-- url     : https://prove2.me/submissions/370e7543-0d35-4816-9c24-ac70fcadeba2

import Definitions.Def_Submission_ThreeSum_SubsetStages
import Definitions.Def_Submission_ThreeSum_MaskDifference
import Definitions.Def_Submission_ThreeSum_QueryCoordinates
import Definitions.Def_Submission_ThreeSum_SignedLeaf

set_option autoImplicit false
open ThreeSum ThreeSum.SignedLeaf
open Finset ThreeSum.SubsetAddress
open scoped BigOperators
namespace ThreeSum.SignedLeaf
theorem _root_.solution {a b : ℕ} (h : b ≤ a) :
    (-1 : ℤ)^(a-b) = (-1 : ℤ)^a*(-1 : ℤ)^b := by
  have ha : a = (a-b)+b := by omega
  rw [ha,pow_add,mul_assoc,← pow_add]
  have hb : b+b = 2*b := by omega
  rw [hb,pow_mul]
  norm_num
end ThreeSum.SignedLeaf
