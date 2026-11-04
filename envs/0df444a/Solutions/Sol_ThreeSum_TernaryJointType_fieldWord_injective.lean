-- Prove2me | solution 1 for ThreeSum.TernaryJointType.fieldWord_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:31:00.025024+00:00
-- url     : https://prove2.me/submissions/74a7943a-8cd4-4787-a0d9-3f90b7112222

import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryJointType
import Theorems.Thm_ThreeSum_TernaryJointType_trit_cast_injective

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryJointType
open Finset
namespace ThreeSum.TernaryJointType
theorem _root_.solution {L p : ℕ} (hp : 2 < p) :
    Function.Injective (fieldWord (L := L) p) := by
  intro a b hab
  funext i
  exact trit_cast_injective hp (congrFun hab i)
end ThreeSum.TernaryJointType
