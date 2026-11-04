-- Prove2me | solution 1 for ThreeSum.TernaryJointType.CertifiedParameters.alpha_positive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:30:48.911195+00:00
-- url     : https://prove2.me/submissions/4336e16d-53eb-44b1-9127-97a832d90704

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
theorem _root_.solution : 0 < alpha0 ∧ 0 < alpha1 ∧ 0 < alpha2 := by
  norm_num [alpha0, alpha1, alpha2]
end ThreeSum.TernaryJointType.CertifiedParameters
