-- Prove2me | solution 1 for ThreeSum.TernaryJointType.CertifiedParameters.endpoint_marginals
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:30:39.119401+00:00
-- url     : https://prove2.me/submissions/b466bb44-81e6-48ae-a18d-506e0eb674f9

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
theorem _root_.solution :
    alpha0 = pi0 + pi1 / 2 + pi2 / 3 ∧
    alpha1 = pi1 / 2 + pi2 / 3 ∧ alpha2 = pi2 / 3 := by
  norm_num [alpha0, alpha1, alpha2, pi0, pi1, pi2]
end ThreeSum.TernaryJointType.CertifiedParameters
