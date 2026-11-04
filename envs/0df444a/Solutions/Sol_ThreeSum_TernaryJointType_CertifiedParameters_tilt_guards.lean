-- Prove2me | solution 1 for ThreeSum.TernaryJointType.CertifiedParameters.tilt_guards
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:31:25.533984+00:00
-- url     : https://prove2.me/submissions/75e2ddf5-3d62-4342-8b25-e13daf8062c7

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
theorem _root_.solution : 0 < bankY ∧ bankY < 1 ∧ 0 < queryZ ∧ queryZ < 1 := by
  norm_num [bankY, queryZ]
end ThreeSum.TernaryJointType.CertifiedParameters
