-- Prove2me | solution 1 for ThreeSum.TernaryTypeCardinality.decode_encode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:56:56.435868+00:00
-- url     : https://prove2.me/submissions/4eacae3f-077d-4f3e-8855-b6284b0061e2

import Definitions.Def_Submission_ThreeSum_TernaryCoverLocal
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sigma
import Definitions.Def_Submission_ThreeSum_TernaryTypeCardinality
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
attribute [local simp] ThreeSum.HashFamily.hashMap_apply



set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryTypeCardinality
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryCoverLocal
set_option maxHeartbeats 2000000
namespace ThreeSum.TernaryTypeCardinality
theorem _root_.solution {L : ℕ} (w : TritWord L) : decode (encode w)=w := by
  funext i
  unfold decode encode positions
  simp only [mem_filter,mem_univ,true_and]
  generalize h : w i=d
  fin_cases d <;> norm_num [Fin.ext_iff]
end ThreeSum.TernaryTypeCardinality
