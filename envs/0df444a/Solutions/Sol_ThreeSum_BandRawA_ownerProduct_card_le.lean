-- Prove2me | solution 1 for ThreeSum.BandRawA.ownerProduct_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:12:59.562992+00:00
-- url     : https://prove2.me/submissions/83ae4469-0918-4994-a9a3-d6dcf8a1ef18

import Definitions.Def_Submission_ThreeSum_BandRawAProduct
import Definitions.Def_Submission_ThreeSum_BandRawAScore
import Theorems.Thm_ThreeSum_BandRawA_ownerProduct_card
import Theorems.Thm_ThreeSum_BandPartition_length_le
import Theorems.Thm_ThreeSum_BandRawA_row_length_le
import Theorems.Thm_ThreeSum_BandWeightedScore_length_le


set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows Finset
open scoped BigOperators
set_option maxHeartbeats 1900000
set_option maxRecDepth 8000
namespace ThreeSum.BandRawA
theorem _root_.solution (nA nB nC g : ℕ) (rs : List Record) (s : ℕ) :
    (ownerProduct nA nB nC g rs s).card ≤ g^3 := by
  rw [ownerProduct_card]
  calc
    _ ≤ g*g*g := Nat.mul_le_mul (Nat.mul_le_mul (row_length_le ..)
      (BandPartition.length_le ..)) (BandPartition.length_le ..)
    _ = _ := by ring
end ThreeSum.BandRawA
