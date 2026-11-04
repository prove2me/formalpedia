-- Prove2me | solution 1 for ThreeSum.TernarySignedLayout.row_physical_read
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:32:18.106616+00:00
-- url     : https://prove2.me/submissions/c37d2692-1338-47a2-9033-ab88072fd766

import Definitions.Def_Submission_ThreeSum_LightTernarySignedRow
import Definitions.Def_Submission_ThreeSum_TernarySignedLayout
import Theorems.Thm_ThreeSum_TernarySignedLayout_offset_lt
import Theorems.Thm_ThreeSum_TernarySignedLayout_offset_involutive
import Theorems.Thm_ThreeSum_TernarySignedLayout_row_logical_read

set_option autoImplicit false
open ThreeSum ThreeSum.TernarySignedLayout
open TernarySignedReduction
namespace ThreeSum.TernarySignedLayout
theorem _root_.solution {μ : ℕ→ℤ} {dst J : ℕ} {f : Coordinate J→ℤ}
    (hrow : LightTernarySignedRow.Row μ dst J f) {i : ℕ} (hi : i<J+2) :
    μ (dst+i)=feature f (offset J i) := by
  have h := row_logical_read hrow (offset_lt hi)
  rwa [offset_involutive hi] at h
end ThreeSum.TernarySignedLayout
