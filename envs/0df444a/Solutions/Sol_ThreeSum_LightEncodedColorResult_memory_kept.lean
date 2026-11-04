-- Prove2me | solution 1 for ThreeSum.LightEncodedColorResult.memory_kept
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:04:37.239849+00:00
-- url     : https://prove2.me/submissions/df02eb9d-8d8f-464b-a1e3-0850d34cc96f

import Definitions.Def_Submission_ThreeSum_EncodedColorSourceRetention
import Definitions.Def_Submission_ThreeSum_LightEncodedColorResult

set_option autoImplicit false
open ThreeSum ThreeSum.LightEncodedColorResult
open Light
namespace ThreeSum.LightEncodedColorResult
theorem _root_.solution (μ : ℕ → ℤ) (prime cover wanted controls bank out len p : ℕ) :
    Kept μ (memory μ prime cover wanted controls bank out len p) out := by
  intro q hq
  unfold memory
  repeat rw [Function.update_of_ne (by omega)]
end ThreeSum.LightEncodedColorResult
