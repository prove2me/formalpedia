-- Prove2me | solution 1 for ThreeSum.TernaryJointType.output_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:29:58.314725+00:00
-- url     : https://prove2.me/submissions/80e7a5db-d4d3-41af-8785-2118f5755369

import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryJointType
namespace ThreeSum.TernaryJointType
open Finset
private theorem sum_indicator_two (a b q : Fin 3)
    (h : a.val + b.val = q.val) :
    (if q = 2 then 1 else 0 : ℕ) =
      (if a = 0 ∧ b = 2 then 1 else 0) +
        (if a = 1 ∧ b = 1 then 1 else 0) +
          (if a = 2 ∧ b = 0 then 1 else 0) := by
  fin_cases a <;> fin_cases b <;> fin_cases q <;> norm_num at h <;> decide
namespace CertifiedParameters
end CertifiedParameters
end ThreeSum.TernaryJointType
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryJointType
open Finset
namespace ThreeSum.TernaryJointType
theorem _root_.solution {L : ℕ} {a b q : TritWord L}
    (hsum : PointwiseSum a b q) :
    digitCount q 2 = jointCount a b 0 2 + jointCount a b 1 1 +
      jointCount a b 2 0 := by
  unfold digitCount jointCount
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  exact sum_indicator_two (a i) (b i) (q i) (hsum i)
end ThreeSum.TernaryJointType
