-- Prove2me | solution 1 for ThreeSum.ReportingHostPairSegments.leftMasks_bounded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:50:48.580944+00:00
-- url     : https://prove2.me/submissions/a48c5090-e6e2-4448-9f37-018d0d871c46

import Definitions.Def_Submission_ThreeSum_LightReportingPairRows
import Definitions.Def_Submission_ThreeSum_ReportingHostPairSegments
import Theorems.Thm_ThreeSum_SubsetAddress_subsetMask_isMask


set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostPairSegments
open Light ThreeSum.SubsetAddress ReportingHostPairEnumeration
set_option linter.unusedSimpArgs false
variable {α β : Type*}
namespace ThreeSum.ReportingHostPairSegments
theorem _root_.solution (L h : ℕ) : ∀ x ∈ leftMasks L h, |x| ≤ ((2^L : ℕ) : ℤ) := by
  intro x hx
  obtain ⟨p,_,rfl⟩ := List.mem_map.mp hx
  rw [Int.abs_natCast]
  exact Int.ofNat_le.mpr (Nat.le_of_lt (subsetMask_isMask p.1).1)
end ThreeSum.ReportingHostPairSegments
