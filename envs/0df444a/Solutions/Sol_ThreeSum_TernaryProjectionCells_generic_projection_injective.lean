-- Prove2me | solution 1 for ThreeSum.TernaryProjectionCells.generic_projection_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:53:13.076238+00:00
-- url     : https://prove2.me/submissions/d58eb542-b761-4b50-ac80-43d6fa35db84

import Definitions.Def_Submission_ThreeSum_TernaryJointType
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryProjectionCells

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 0
open ThreeSum ThreeSum.TernaryProjectionCells
variable {K : Type*} [Field K]
namespace ThreeSum.TernaryProjectionCells
theorem _root_.solution {a b : K}
    (ha : a ≠ 0) (hb : b ≠ 0) (h2 : (2 : K) ≠ 0)
    (hsum : a+b ≠ 0) (heq : a ≠ b) (hhalf : 2*a ≠ b) (hdouble : a ≠ 2*b) :
    Function.Injective (projectedCell a b) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> norm_num [projectedCell] at h ⊢
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
end ThreeSum.TernaryProjectionCells
