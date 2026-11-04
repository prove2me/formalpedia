-- Prove2me | solution 1 for ThreeSum.LightLocalCoverLayout.space_shift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:49:53.696199+00:00
-- url     : https://prove2.me/submissions/8ff0b079-0889-4b05-b9b2-f2ba247d9115

import Definitions.Def_Submission_ThreeSum_LightLocalCoverBuild
import Definitions.Def_Submission_ThreeSum_LightLocalCoverLayout

set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalCoverLayout
open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverTables
namespace ThreeSum.LightLocalCoverLayout
theorem _root_.solution (base h : ℕ) : space base h = base+space 0 h := by
  unfold space scheduleMaps work matrixPtr hist1 hist0 raw1 raw0 maps bitPtr LightLocalCoverCandidate.space
  omega
end ThreeSum.LightLocalCoverLayout
