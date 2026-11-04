-- Prove2me | solution 1 for ThreeSum.TernaryJointType.CertifiedParameters.cutoff_guard
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:31:10.523902+00:00
-- url     : https://prove2.me/submissions/4eed878b-7af9-47bc-878d-2ba0e38ca40b

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
theorem _root_.solution : 0 < deficit ∧ deficit < (pi1 + 2 * pi2) / 2 := by
  norm_num [deficit, pi1, pi2]
end ThreeSum.TernaryJointType.CertifiedParameters
