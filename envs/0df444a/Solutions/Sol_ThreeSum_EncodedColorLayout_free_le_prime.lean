-- Prove2me | solution 1 for ThreeSum.EncodedColorLayout.free_le_prime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:09:22.415509+00:00
-- url     : https://prove2.me/submissions/947d1119-68ee-47ee-9436-213b6774fe97

import Definitions.Def_Submission_ThreeSum_EncodedColorPrimeData
import Definitions.Def_Submission_ThreeSum_LightBandRawAColor
import Definitions.Def_Submission_ThreeSum_EncodedColorLayout
import Theorems.Thm_ThreeSum_EncodedColorLayout_free_le_normalizedEnd

set_option autoImplicit false
open ThreeSum ThreeSum.EncodedColorLayout
namespace ThreeSum.EncodedColorLayout
theorem _root_.solution (free n g : ℕ) : free+8 ≤ prime free n g := by
  have h := free_le_normalizedEnd free n g
  unfold prime
  omega
end ThreeSum.EncodedColorLayout
