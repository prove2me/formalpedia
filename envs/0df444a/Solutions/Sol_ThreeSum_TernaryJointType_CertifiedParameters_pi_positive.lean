-- Prove2me | solution 1 for ThreeSum.TernaryJointType.CertifiedParameters.pi_positive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:30:47.918288+00:00
-- url     : https://prove2.me/submissions/e99c1543-a38b-4cde-8547-caf99e2eb25c

import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryJointType

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryJointType
open Finset
open ThreeSum.TernaryJointType.CertifiedParameters
namespace ThreeSum.TernaryJointType.CertifiedParameters
theorem _root_.solution : 0 < pi0 ∧ 0 < pi1 ∧ 0 < pi2 := by
  norm_num [pi0, pi1, pi2]
end ThreeSum.TernaryJointType.CertifiedParameters
