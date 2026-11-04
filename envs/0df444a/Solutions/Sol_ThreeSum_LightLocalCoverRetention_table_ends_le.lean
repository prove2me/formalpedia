-- Prove2me | solution 1 for ThreeSum.LightLocalCoverRetention.table_ends_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:28:45.461966+00:00
-- url     : https://prove2.me/submissions/20bbcb16-3215-4b8f-a1db-9eaf70145a36

import Definitions.Def_Submission_ThreeSum_LightLocalCoverInit
import Definitions.Def_Submission_ThreeSum_LightLocalCoverRetention

set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalCoverRetention
open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverTables
open LightLocalCoverLayout LightLocalCoverMetadata
set_option maxHeartbeats 1000000
namespace ThreeSum.LightLocalCoverRetention
theorem _root_.solution (base h : ℕ) :
    maps base h+rows h*(2*(512*h)) ≤ nextFree base h ∧
    hist0 base h+rows h*localPrime h ≤ nextFree base h ∧
    hist1 base h+rows h*localPrime h ≤ nextFree base h ∧
    matrixPtr base h+rows h*cols h ≤ nextFree base h ∧
    candidates base h+scheduleSize h ≤ nextFree base h := by
  unfold nextFree scheduleMaps candidates work matrixPtr hist1 hist0 raw1 raw0 maps bitPtr
    LightCoverGreedy.total LightCoverGreedy.out
  omega
end ThreeSum.LightLocalCoverRetention
