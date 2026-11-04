-- Prove2me | solution 1 for ThreeSum.BandScales.typedOutputs_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:04:49.007999+00:00
-- url     : https://prove2.me/submissions/d028ad56-23b0-4650-8325-5461dfdaae28

import Definitions.Def_Submission_ThreeSum_TrimScales
import Definitions.Def_Submission_ThreeSum_BandScales

set_option autoImplicit false
open ThreeSum ThreeSum.BandScales
open Filter Real ThreeSum.Scales
open scoped Topology
namespace ThreeSum.BandScales
theorem _root_.solution (n : ℕ) : 0 < typedOutputs n := by
  unfold typedOutputs
  exact Nat.pow_pos (Nat.choose_pos (by omega))
end ThreeSum.BandScales
