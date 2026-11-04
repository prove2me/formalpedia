-- Prove2me | solution 1 for ThreeSum.BandScales.bandRoot_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:06:15.745381+00:00
-- url     : https://prove2.me/submissions/49e79600-0b53-45fa-82c0-09d175f488ac

import Definitions.Def_Submission_ThreeSum_TrimScales
import Definitions.Def_Submission_ThreeSum_BandScales

set_option autoImplicit false
open ThreeSum ThreeSum.BandScales
open Filter Real ThreeSum.Scales
open scoped Topology
namespace ThreeSum.BandScales
theorem _root_.solution (n : ℕ) : 0 < bandRoot n := LocalCoverBounds.rootCeiling_pos _
end ThreeSum.BandScales
