-- Prove2me | solution 1 for ThreeSum.TernaryEuler.weight_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:01:38.149327+00:00
-- url     : https://prove2.me/submissions/68545777-9b48-4365-be18-e44cd0523906

import Definitions.Def_Submission_ThreeSum_TernaryQuery
import Definitions.Def_Submission_ThreeSum_TernaryEuler

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryEuler
open Finset
open ThreeSum.TernaryJointType ThreeSum.TernaryBank
namespace ThreeSum.TernaryEuler
theorem _root_.solution {N : ℕ} (R A : TritWord N) (i : Fin N) :
    weight R A = digitChoose (R i) (A i) *
      ∏ j ∈ (univ : Finset (Fin N)).erase i, digitChoose (R j) (A j) := by
  exact (Finset.mul_prod_erase univ _ (mem_univ i)).symm
end ThreeSum.TernaryEuler
