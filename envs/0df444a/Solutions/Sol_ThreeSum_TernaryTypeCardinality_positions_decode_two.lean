-- Prove2me | solution 1 for ThreeSum.TernaryTypeCardinality.positions_decode_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:21:22.244499+00:00
-- url     : https://prove2.me/submissions/514b2450-7f10-499a-ab70-28d961431f3b

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
theorem _root_.solution {L : ℕ} (p : Pair L) : positions (decode p) 2=p.1 := by
  ext i
  simp only [positions,mem_filter,mem_univ,true_and,decode]
  by_cases ht : i∈p.1 <;> by_cases ho : i∈p.2 <;> simp [ht,ho,Fin.ext_iff]
end ThreeSum.TernaryTypeCardinality
