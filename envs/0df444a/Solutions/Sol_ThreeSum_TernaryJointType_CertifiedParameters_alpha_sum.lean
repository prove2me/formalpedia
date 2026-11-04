-- Prove2me | solution 1 for ThreeSum.TernaryJointType.CertifiedParameters.alpha_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:30:38.102927+00:00
-- url     : https://prove2.me/submissions/0f636fa3-f332-48d3-b652-34e614b088f0

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
theorem _root_.solution : alpha0 + alpha1 + alpha2 = 1 := by
  norm_num [alpha0, alpha1, alpha2]
end ThreeSum.TernaryJointType.CertifiedParameters
