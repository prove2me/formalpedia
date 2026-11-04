-- Prove2me | solution 1 for ThreeSum.TernaryJointType.jointCount_row
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:29:04.007923+00:00
-- url     : https://prove2.me/submissions/0866eb82-7e4c-4347-8b6a-2d4309620224

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
theorem _root_.solution {L : ℕ} (a b : TritWord L) (u : Fin 3) :
    ∑ v : Fin 3, jointCount a b u v = digitCount a u := by
  unfold jointCount digitCount
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases ha : a i = u <;> simp [ha]
end ThreeSum.TernaryJointType
