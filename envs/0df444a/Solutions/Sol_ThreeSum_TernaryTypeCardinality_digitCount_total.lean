-- Prove2me | solution 1 for ThreeSum.TernaryTypeCardinality.digitCount_total
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:56:55.25061+00:00
-- url     : https://prove2.me/submissions/c9f5cbe8-d98f-4fba-b300-a5483a2f26ea

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
theorem _root_.solution {L : ℕ} (w : TritWord L) :
    digitCount w 0+digitCount w 1+digitCount w 2=L := by
  unfold digitCount
  rw [←Finset.sum_add_distrib,←Finset.sum_add_distrib]
  have hlocal (d : Fin 3) : (if d=0 then 1 else 0)+
      (if d=1 then 1 else 0)+(if d=2 then 1 else 0 : ℕ)=1 := by
    fin_cases d <;> norm_num [Fin.ext_iff]
  simp_rw [hlocal]
  simp
end ThreeSum.TernaryTypeCardinality
