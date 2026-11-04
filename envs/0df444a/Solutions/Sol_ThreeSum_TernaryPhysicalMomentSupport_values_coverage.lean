-- Prove2me | solution 1 for ThreeSum.TernaryPhysicalMomentSupport.values_coverage
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:21:52.408924+00:00
-- url     : https://prove2.me/submissions/d1176be8-bf99-4b10-9bf7-65e819a7b4eb

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
theorem _root_.solution (mode : P → ℤ) (a : P) : ∃ i, values mode i=mode a := by
  let d : {d : ℤ // d∈support mode} := ⟨mode a,mem_image.mpr ⟨a,mem_univ _,rfl⟩⟩
  refine ⟨(enumeration mode).symm d,?_⟩
  exact congrArg Subtype.val ((enumeration mode).apply_symm_apply d)
end ThreeSum.TernaryPhysicalMomentSupport
