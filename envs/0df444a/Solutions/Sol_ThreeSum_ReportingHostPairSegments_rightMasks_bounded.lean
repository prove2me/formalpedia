-- Prove2me | solution 1 for ThreeSum.ReportingHostPairSegments.rightMasks_bounded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:50:49.896828+00:00
-- url     : https://prove2.me/submissions/594bb009-b7d9-4366-ab75-e5d97acb0315

import Definitions.Def_Submission_ThreeSum_LightReportingPairRows
import Definitions.Def_Submission_ThreeSum_ReportingHostPairSegments
import Theorems.Thm_ThreeSum_SubsetAddress_subsetMask_isMask


set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostPairSegments
open Light ThreeSum.SubsetAddress ReportingHostPairEnumeration
set_option linter.unusedSimpArgs false
variable {α β : Type*}
namespace ThreeSum.ReportingHostPairSegments
theorem _root_.solution (L h : ℕ) : ∀ x ∈ rightMasks L h, |x| ≤ ((2^L : ℕ) : ℤ) := by
  intro x hx
  obtain ⟨p,_,rfl⟩ := List.mem_map.mp hx
  rw [Int.abs_natCast]
  exact Int.ofNat_le.mpr (Nat.le_of_lt (subsetMask_isMask p.2).1)
end ThreeSum.ReportingHostPairSegments
