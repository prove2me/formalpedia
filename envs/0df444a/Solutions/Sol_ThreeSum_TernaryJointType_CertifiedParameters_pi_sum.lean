-- Prove2me | solution 1 for ThreeSum.TernaryJointType.CertifiedParameters.pi_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:30:37.057206+00:00
-- url     : https://prove2.me/submissions/230c9653-d06c-4530-95bd-2bdb71b85c44

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
theorem _root_.solution : pi0 + pi1 + pi2 = 1 := by
  norm_num [pi0, pi1, pi2]
end ThreeSum.TernaryJointType.CertifiedParameters
