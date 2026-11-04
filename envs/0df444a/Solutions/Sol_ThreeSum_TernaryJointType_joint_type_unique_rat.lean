-- Prove2me | solution 1 for ThreeSum.TernaryJointType.joint_type_unique_rat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:30:11.556209+00:00
-- url     : https://prove2.me/submissions/6d5da5b0-8685-4d29-8af8-76e51c86c1b4

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
theorem _root_.solution
    (x00 x01 x02 x10 x11 x20 p0 p1 p2 a1 a2 : ℚ)
    (h00 : x00 = p0) (h02 : x02 = a2) (h20 : x20 = a2)
    (hrow1 : x10 + x11 = a1) (hcol1 : x01 + x11 = a1)
    (hout1 : x01 + x10 = p1) (hout2 : x02 + x11 + x20 = p2)
    (hthirds : p2 = 3 * a2) :
    x00 = p0 ∧ x01 = p1 / 2 ∧ x10 = p1 / 2 ∧
      x02 = p2 / 3 ∧ x11 = p2 / 3 ∧ x20 = p2 / 3 := by
  refine ⟨h00, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith
end ThreeSum.TernaryJointType
