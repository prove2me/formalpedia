-- Prove2me | solution 1 for ThreeSum.LightEncodedColorLayout.headMemory_kept
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:06:19.891089+00:00
-- url     : https://prove2.me/submissions/93c70e81-a7de-4d14-9f9c-f8439d29cbeb

import Definitions.Def_Submission_ThreeSum_EncodedColorLayout
import Definitions.Def_Submission_ThreeSum_LightEncodedColorLayout

set_option autoImplicit false
open ThreeSum ThreeSum.LightEncodedColorLayout
open Light BandPartition EncodedColorLayout
set_option maxHeartbeats 2200000
set_option maxRecDepth 11000
namespace ThreeSum.LightEncodedColorLayout
theorem _root_.solution (μ : ℕ → ℤ) (free n g : ℕ) : Kept μ (headMemory μ free n g) free := by
  intro q hq
  unfold headMemory
  repeat rw [Function.update_of_ne (by omega)]
end ThreeSum.LightEncodedColorLayout
