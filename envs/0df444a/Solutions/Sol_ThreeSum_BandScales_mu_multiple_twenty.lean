-- Prove2me | solution 1 for ThreeSum.BandScales.mu_multiple_twenty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:45:28.949672+00:00
-- url     : https://prove2.me/submissions/900362e5-50d0-41c7-8004-30e527de6dae

import Definitions.Def_Submission_ThreeSum_TrimScales
import Definitions.Def_Submission_ThreeSum_BandScales

set_option autoImplicit false
open ThreeSum ThreeSum.BandScales
open Filter Real ThreeSum.Scales
open scoped Topology
namespace ThreeSum.BandScales
theorem _root_.solution (n : ℕ) : 20 ∣ mu n := by
  unfold mu totalSize blockCount
  exact ⟨(inputBits n / (100 * microSize (inputBits n))) * microSize (inputBits n), by ring⟩
end ThreeSum.BandScales
