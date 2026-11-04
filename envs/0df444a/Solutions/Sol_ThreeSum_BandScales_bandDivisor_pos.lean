-- Prove2me | solution 1 for ThreeSum.BandScales.bandDivisor_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:04:40.30588+00:00
-- url     : https://prove2.me/submissions/5ccd78f1-36b2-443b-bf6e-c5e88df5a23d

import Definitions.Def_Submission_ThreeSum_TrimScales
import Definitions.Def_Submission_ThreeSum_BandScales

set_option autoImplicit false
open ThreeSum ThreeSum.BandScales
open Filter Real ThreeSum.Scales
open scoped Topology
namespace ThreeSum.BandScales
theorem _root_.solution (n : ℕ) : 0 < bandDivisor n := by
  unfold bandDivisor
  positivity
end ThreeSum.BandScales
