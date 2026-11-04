-- Prove2me | solution 1 for ThreeSum.LightLocalCoverLayout.work_le_space
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:14:29.213801+00:00
-- url     : https://prove2.me/submissions/a580746c-8cdd-4e74-9a67-5f7a1dafe622

import Definitions.Def_Submission_ThreeSum_LightLocalCoverBuild
import Definitions.Def_Submission_ThreeSum_LightLocalCoverLayout

set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalCoverLayout
open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverTables
namespace ThreeSum.LightLocalCoverLayout
theorem _root_.solution (base h : ℕ) : work base h ≤ space base h := by
  have hm := Nat.le_max_left
    (LightLocalCoverCandidate.space (work base h) (512*h) (vertices h) (localPrime h))
    (scheduleMaps base h+scheduleSize h*(2*(512*h)))
  change LightLocalCoverCandidate.space (work base h) (512*h) (vertices h) (localPrime h) ≤ space base h at hm
  unfold LightLocalCoverCandidate.space at hm
  omega
end ThreeSum.LightLocalCoverLayout
