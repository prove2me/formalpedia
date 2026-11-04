-- Prove2me | solution 1 for ThreeSum.LightTernaryMetadata.writeRecord_kept
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:24:36.919558+00:00
-- url     : https://prove2.me/submissions/cdb44538-6d50-4467-ad63-6306c91ff2e8

import Definitions.Def_Submission_ThreeSum_LightTernaryCodes
import Definitions.Def_Submission_ThreeSum_LightTernaryMetadata

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryMetadata
open Light ThreeSum.LightSubsetAddress ThreeSum.MaskErase
set_option maxHeartbeats 3000000
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightTernaryMetadata
theorem _root_.solution {μ : ℕ → ℤ} {base n j : ℕ} {q z0 z1 m : ℤ}
    (hj : j < n) : SameOutside μ (writeRecord μ base n j q z0 z1 m) base (4*n) := by
  intro x hx
  unfold writeRecord
  rw [Function.update_of_ne (by rcases hx with h | h <;> omega),
    Function.update_of_ne (by rcases hx with h | h <;> omega),
    Function.update_of_ne (by rcases hx with h | h <;> omega),
    Function.update_of_ne (by rcases hx with h | h <;> omega)]
end ThreeSum.LightTernaryMetadata
