-- Prove2me | solution 1 for ThreeSum.TernaryJointType.fieldWord_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:30:25.630091+00:00
-- url     : https://prove2.me/submissions/cad9fddc-d43e-42b3-a261-6133606aef50

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
theorem _root_.solution {L p : ℕ} {a b q : TritWord L}
    (hsum : PointwiseSum a b q) :
    ∀ i, fieldWord p a i + fieldWord p b i = fieldWord p q i := by
  intro i
  unfold fieldWord
  rw [← Nat.cast_add, hsum i]
end ThreeSum.TernaryJointType
