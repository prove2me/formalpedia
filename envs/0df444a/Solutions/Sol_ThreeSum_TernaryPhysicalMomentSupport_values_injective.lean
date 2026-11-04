-- Prove2me | solution 1 for ThreeSum.TernaryPhysicalMomentSupport.values_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:11:02.102478+00:00
-- url     : https://prove2.me/submissions/6a3756b9-fee3-4653-a8cf-4e89de8e08c3

import Definitions.Def_Submission_ThreeSum_FiniteMomentZeroDetector
import Mathlib.Data.Finset.Sort
import Definitions.Def_Submission_ThreeSum_TernaryPhysicalMomentSupport

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryPhysicalMomentSupport
open Finset FiniteMomentZeroDetector
open scoped BigOperators
variable {P : Type*} [Fintype P]
set_option maxHeartbeats 3000000
namespace ThreeSum.TernaryPhysicalMomentSupport
theorem _root_.solution (mode : P → ℤ) : Function.Injective (values mode) := by
  intro i j hij
  apply (enumeration mode).injective
  exact Subtype.ext hij
end ThreeSum.TernaryPhysicalMomentSupport
