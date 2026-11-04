-- Prove2me | solution 1 for ThreeSum.TernaryJointType.edge_joint_type
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:30:59.006883+00:00
-- url     : https://prove2.me/submissions/c1bbb695-1fc4-4836-91c2-4b97f00632b8

import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryJointType
import Theorems.Thm_ThreeSum_TernaryJointType_jointCount_row
import Theorems.Thm_ThreeSum_TernaryJointType_jointCount_col
import Theorems.Thm_ThreeSum_TernaryJointType_jointCount_forbidden
import Theorems.Thm_ThreeSum_TernaryJointType_output_zero
import Theorems.Thm_ThreeSum_TernaryJointType_output_one
import Theorems.Thm_ThreeSum_TernaryJointType_output_two
import Theorems.Thm_ThreeSum_TernaryJointType_joint_type_unique_nat

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryJointType
open Finset
namespace ThreeSum.TernaryJointType
theorem _root_.solution {L : ℕ} {α π : DigitType} {a b q : TritWord L}
    (hedge : Edge α π a b q) (hthirds : π 2 = 3 * α 2) :
    jointCount a b 0 0 = π 0 ∧
      jointCount a b 0 1 = π 1 / 2 ∧
      jointCount a b 1 0 = π 1 / 2 ∧
      jointCount a b 0 2 = π 2 / 3 ∧
      jointCount a b 1 1 = π 2 / 3 ∧
      jointCount a b 2 0 = π 2 / 3 := by
  rcases hedge with ⟨ha, hb, hq, hs⟩
  have hz12 := jointCount_forbidden hs (1 : Fin 3) (2 : Fin 3) (by decide)
  have hz21 := jointCount_forbidden hs (2 : Fin 3) (1 : Fin 3) (by decide)
  have hz22 := jointCount_forbidden hs (2 : Fin 3) (2 : Fin 3) (by decide)
  have hr2 : jointCount a b 2 0 = α 2 := by
    have h := (jointCount_row a b (2 : Fin 3)).trans (ha 2)
    simpa [Fin.sum_univ_three, hz21, hz22] using h
  have hc2 : jointCount a b 0 2 = α 2 := by
    have h := (jointCount_col a b (2 : Fin 3)).trans (hb 2)
    simpa [Fin.sum_univ_three, hz12, hz22] using h
  have hr1 : jointCount a b 1 0 + jointCount a b 1 1 = α 1 := by
    have h := (jointCount_row a b (1 : Fin 3)).trans (ha 1)
    simpa [Fin.sum_univ_three, hz12] using h
  have hc1 : jointCount a b 0 1 + jointCount a b 1 1 = α 1 := by
    have h := (jointCount_col a b (1 : Fin 3)).trans (hb 1)
    simpa [Fin.sum_univ_three, hz21] using h
  have ho0 : jointCount a b 0 0 = π 0 := (output_zero hs).symm.trans (hq 0)
  have ho1 : jointCount a b 0 1 + jointCount a b 1 0 = π 1 :=
    (output_one hs).symm.trans (hq 1)
  have ho2 : jointCount a b 0 2 + jointCount a b 1 1 + jointCount a b 2 0 = π 2 :=
    (output_two hs).symm.trans (hq 2)
  exact joint_type_unique_nat _ _ _ _ _ _ _ _ _ _ _
    ho0 hc2 hr2 hr1 hc1 ho1 ho2 hthirds
end ThreeSum.TernaryJointType
