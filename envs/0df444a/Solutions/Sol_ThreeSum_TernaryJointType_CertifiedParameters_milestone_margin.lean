-- Prove2me | solution 1 for ThreeSum.TernaryJointType.CertifiedParameters.milestone_margin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:31:26.586211+00:00
-- url     : https://prove2.me/submissions/a00e43a3-8c80-4c2a-96de-2f4827cee830

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
theorem _root_.solution : target192028 < target1921 := by
  norm_num [target192028, target1921]
end ThreeSum.TernaryJointType.CertifiedParameters
