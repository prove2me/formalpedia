-- Prove2me | solution 1 for ThreeSum.TernaryJointType.jointCount_forbidden
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:29:05.824123+00:00
-- url     : https://prove2.me/submissions/81a20938-cb83-4f04-9324-833f9beff24c

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
theorem _root_.solution {L : ℕ} {a b q : TritWord L}
    (hsum : PointwiseSum a b q) (u v : Fin 3) (hlarge : 2 < u.val + v.val) :
    jointCount a b u v = 0 := by
  unfold jointCount
  apply Finset.sum_eq_zero
  intro i hi
  have hnot : ¬ (a i = u ∧ b i = v) := by
    intro h
    have hq := (q i).isLt
    have hs := hsum i
    rw [h.1, h.2] at hs
    omega
  simp [hnot]
end ThreeSum.TernaryJointType
