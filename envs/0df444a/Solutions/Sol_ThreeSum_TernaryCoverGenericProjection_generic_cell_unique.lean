-- Prove2me | solution 1 for ThreeSum.TernaryCoverGenericProjection.generic_cell_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:53:14.307547+00:00
-- url     : https://prove2.me/submissions/3aafbff2-c056-458d-8279-49a05b346dc0

import Definitions.Def_Submission_ThreeSum_TernaryProjectionCells
import Definitions.Def_Submission_ThreeSum_TernaryCoverLocal
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryCoverGenericProjection
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
attribute [local simp] ThreeSum.HashFamily.hashMap_apply



set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open ThreeSum ThreeSum.TernaryCoverGenericProjection
open Finset TernaryJointType TernaryCoverLocal
variable {K : Type*} [Field K]
namespace ThreeSum.TernaryCoverGenericProjection
theorem _root_.solution {a b : K}
    (ha : a ≠ 0) (hb : b ≠ 0) (h2 : (2 : K) ≠ 0)
    (hsum : a+b ≠ 0) (heq : a ≠ b) (hhalf : 2*a ≠ b) (hdouble : a ≠ 2*b)
    (x y u v : Fin 3) (hxy : x.val+y.val ≤ 2) (huv : u.val+v.val ≤ 2)
    (h : a*(x.val : K)+b*(y.val : K) = a*(u.val : K)+b*(v.val : K)) :
    x = u ∧ y = v := by
  fin_cases x <;> fin_cases y <;> fin_cases u <;> fin_cases v <;> norm_num at hxy
  all_goals norm_num at huv
  all_goals norm_num at h
  all_goals norm_num
  all_goals try simp only [h2, or_false, false_or] at h
  all_goals first
    | (apply ha; linear_combination h)
    | (apply ha; linear_combination -h)
    | (apply hb; linear_combination h)
    | (apply hb; linear_combination -h)
    | (apply hsum; linear_combination h)
    | (apply hsum; linear_combination -h)
    | (apply heq; linear_combination h)
    | (apply heq; linear_combination -h)
    | (apply hhalf; linear_combination h)
    | (apply hhalf; linear_combination -h)
    | (apply hdouble; linear_combination h)
    | (apply hdouble; linear_combination -h)
end ThreeSum.TernaryCoverGenericProjection
