-- Prove2me | solution 1 for ThreeSum.TernaryJointType.jointCount_col
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:29:04.868059+00:00
-- url     : https://prove2.me/submissions/f68d6f74-f553-4b06-818c-04005ce23333

import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryJointType

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryJointType
open Finset
namespace ThreeSum.TernaryJointType
theorem _root_.solution {L : ℕ} (a b : TritWord L) (v : Fin 3) :
    ∑ u : Fin 3, jointCount a b u v = digitCount b v := by
  unfold jointCount digitCount
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hb : b i = v <;> simp [hb]
end ThreeSum.TernaryJointType
