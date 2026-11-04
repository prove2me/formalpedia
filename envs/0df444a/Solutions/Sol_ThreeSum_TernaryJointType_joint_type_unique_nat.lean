-- Prove2me | solution 1 for ThreeSum.TernaryJointType.joint_type_unique_nat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:30:10.543221+00:00
-- url     : https://prove2.me/submissions/2249933d-0f69-4de2-9d52-c772590ab332

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
    (x00 x01 x02 x10 x11 x20 p0 p1 p2 a1 a2 : ℕ)
    (h00 : x00 = p0) (h02 : x02 = a2) (h20 : x20 = a2)
    (hrow1 : x10 + x11 = a1) (hcol1 : x01 + x11 = a1)
    (hout1 : x01 + x10 = p1) (hout2 : x02 + x11 + x20 = p2)
    (hthirds : p2 = 3 * a2) :
    x00 = p0 ∧ x01 = p1 / 2 ∧ x10 = p1 / 2 ∧
      x02 = p2 / 3 ∧ x11 = p2 / 3 ∧ x20 = p2 / 3 := by
  omega
end ThreeSum.TernaryJointType
