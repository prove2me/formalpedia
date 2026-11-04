-- Prove2me | solution 1 for ThreeSum.TernaryPhysicalMomentSupport.weights_positive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:21:54.650242+00:00
-- url     : https://prove2.me/submissions/b7a2b818-b4de-4e87-8632-1048c18c8bed

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
theorem _root_.solution (mode mass : P → ℤ) (hm : ∀ a, 0<mass a)
    (i : Fin (support mode).card) : 0<weights mode mass i := by
  unfold weights
  apply sum_pos'
  · intro a ha
    split_ifs <;> first | exact (hm a).le | rfl
  · have hmem := (enumeration mode i).property
    obtain ⟨a,ha,he⟩ := mem_image.mp hmem
    refine ⟨a,mem_univ _,?_⟩
    have hv : mode a=values mode i := he
    simpa only [if_pos hv] using hm a
end ThreeSum.TernaryPhysicalMomentSupport
