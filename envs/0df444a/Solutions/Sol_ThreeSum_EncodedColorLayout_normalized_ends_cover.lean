-- Prove2me | solution 1 for ThreeSum.EncodedColorLayout.normalized_ends_cover
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:55:15.598202+00:00
-- url     : https://prove2.me/submissions/9c855d29-d2cf-4355-8755-f3476857aec5

import Definitions.Def_Submission_ThreeSum_EncodedColorPrimeData
import Definitions.Def_Submission_ThreeSum_LightBandRawAColor
import Definitions.Def_Submission_ThreeSum_EncodedColorLayout
import Theorems.Thm_ThreeSum_EncodedColorLayout_normalized_ends_before_count
import Theorems.Thm_ThreeSum_EncodedColorLayout_prime_le_cover

set_option autoImplicit false
open ThreeSum ThreeSum.EncodedColorLayout
namespace ThreeSum.EncodedColorLayout
theorem _root_.solution (free n g M y : ℕ) :
    av free n+n ≤ cover free n g M y ∧ ae free n+2+2*n ≤ cover free n g M y ∧
    bv free n+n ≤ cover free n g M y ∧ be free n+2+2*n ≤ cover free n g M y ∧
    cv free n+n ≤ cover free n g M y ∧ ce free n+2+2*n ≤ cover free n g M y ∧
    tables free n+ColorBandBounds.count n g ≤ cover free n g M y ∧
    rec free n g+4*ColorBandBounds.count n g ≤ cover free n g M y ∧
    LightBandRawA.space (vals free n g) (ColorBandBounds.count n g) g ≤ cover free n g M y := by
  obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩ := normalized_ends_before_count free n g
  have h := prime_le_cover free n g M y
  change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ normalizedEnd free n g ≤ _
  unfold prime at h
  omega
end ThreeSum.EncodedColorLayout
