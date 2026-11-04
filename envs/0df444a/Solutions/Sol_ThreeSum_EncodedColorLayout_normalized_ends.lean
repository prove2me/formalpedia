-- Prove2me | solution 1 for ThreeSum.EncodedColorLayout.normalized_ends
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:01:42.545054+00:00
-- url     : https://prove2.me/submissions/61b3da57-ba1d-4551-abd8-7d9270c066bc

import Definitions.Def_Submission_ThreeSum_EncodedColorPrimeData
import Definitions.Def_Submission_ThreeSum_LightBandRawAColor
import Definitions.Def_Submission_ThreeSum_EncodedColorLayout
import Theorems.Thm_ThreeSum_EncodedColorLayout_normalized_ends_before_count

set_option autoImplicit false
open ThreeSum ThreeSum.EncodedColorLayout
namespace ThreeSum.EncodedColorLayout
theorem _root_.solution (free n g : ℕ) :
    av free n+n ≤ prime free n g ∧ ae free n+2+2*n ≤ prime free n g ∧
    bv free n+n ≤ prime free n g ∧ be free n+2+2*n ≤ prime free n g ∧
    cv free n+n ≤ prime free n g ∧ ce free n+2+2*n ≤ prime free n g ∧
    tables free n+ColorBandBounds.count n g ≤ prime free n g ∧
    rec free n g+4*ColorBandBounds.count n g ≤ prime free n g := by
  obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩ := normalized_ends_before_count free n g
  unfold prime
  omega
end ThreeSum.EncodedColorLayout
