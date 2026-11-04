-- Prove2me | solution 1 for ThreeSum.TernaryPhysicalMomentSupport.target_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:25:33.138304+00:00
-- url     : https://prove2.me/submissions/467df3da-44ac-45c2-8a58-f5c5eea3a302

import Definitions.Def_Submission_ThreeSum_FiniteMomentZeroDetector
import Mathlib.Data.Finset.Sort
import Definitions.Def_Submission_ThreeSum_TernaryPhysicalMomentSupport
import Theorems.Thm_ThreeSum_TernaryPhysicalMomentSupport_values_coverage

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryPhysicalMomentSupport
open Finset FiniteMomentZeroDetector
open scoped BigOperators
variable {P : Type*} [Fintype P]
set_option maxHeartbeats 3000000
namespace ThreeSum.TernaryPhysicalMomentSupport
theorem _root_.solution (mode : P → ℤ) (target : ℤ) :
    (∃ i, values mode i=target) ↔ ∃ a, mode a=target := by
  constructor
  · rintro ⟨i,hi⟩
    have hmem := (enumeration mode i).property
    obtain ⟨a,ha,he⟩ := mem_image.mp hmem
    exact ⟨a,he.trans hi⟩
  · rintro ⟨a,ha⟩
    obtain ⟨i,hi⟩ := values_coverage mode a
    exact ⟨i,hi.trans ha⟩
end ThreeSum.TernaryPhysicalMomentSupport
