-- Prove2me | solution 1 for ThreeSum.TernaryCoverProjection.doubledAmbiguous_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:54:53.672845+00:00
-- url     : https://prove2.me/submissions/98fee4fd-bfc3-4e1a-a535-9c15888a9444

import Definitions.Def_Submission_ThreeSum_TernaryCoverLocal
import Mathlib.Data.Finset.Powerset
import Definitions.Def_Submission_ThreeSum_TernaryCoverProjection
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_TernaryCoverLocal_edge_data
import Theorems.Thm_ThreeSum_TernaryJointType_edge_joint_type
attribute [local simp] ThreeSum.HashFamily.hashMap_apply


noncomputable section
namespace ThreeSum.TernaryCoverProjection
open Finset TernaryJointType TernaryCoverLocal
private theorem doubled_indicator (swap : Bool) (a b : Fin 3)
    (hab : a.val + b.val ≤ 2) :
    (if doubledCode swap a b = 2 then 1 else 0 : ℕ) =
      if swap then (if a = 0 ∧ b = 1 then 1 else 0) + (if a = 2 ∧ b = 0 then 1 else 0)
      else (if a = 1 ∧ b = 0 then 1 else 0) + (if a = 0 ∧ b = 2 then 1 else 0) := by
  cases swap <;> fin_cases a <;> fin_cases b <;> norm_num [doubledCode, Fin.ext_iff] at *
end ThreeSum.TernaryCoverProjection
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverProjection
open Finset TernaryJointType TernaryCoverLocal
namespace ThreeSum.TernaryCoverProjection
theorem _root_.solution {L : ℕ} {α π : DigitType} (swap : Bool) (e : LocalEdge L α π)
    (hthirds : π 2 = 3 * α 2) :
    (doubledAmbiguous swap e).card = π 1 / 2 + π 2 / 3 := by
  have htype := edge_joint_type (edge_data e) hthirds
  have hind (i : Fin L) := doubled_indicator swap (left e i) (right e i)
    (by have hs := (edge_data e).2.2.2 i; have hq := (output e i).isLt; omega)
  unfold doubledAmbiguous
  rw [card_eq_sum_ones, sum_filter]
  simp_rw [hind]
  cases swap
  · simp only [Bool.false_eq_true, ite_false, sum_add_distrib]
    change jointCount (left e) (right e) 1 0 + jointCount (left e) (right e) 0 2 = _
    rw [htype.2.2.1, htype.2.2.2.1]
  · simp only [ite_true, sum_add_distrib]
    change jointCount (left e) (right e) 0 1 + jointCount (left e) (right e) 2 0 = _
    rw [htype.2.1, htype.2.2.2.2.2]
end ThreeSum.TernaryCoverProjection
