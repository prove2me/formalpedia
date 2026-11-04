-- Prove2me | solution 1 for ThreeSum.LightOriginalOffset.time_bound_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:17:36.554314+00:00
-- url     : https://prove2.me/submissions/91cc1135-84c7-4651-8366-f157644237cc

import Definitions.Def_Submission_ThreeSum_LightBalancedOffset
import Definitions.Def_Submission_ThreeSum_LightModuloCounts
import Definitions.Def_Submission_ThreeSum_LightOriginalOffset
import Theorems.Thm_ThreeSum_KaratsubaInterface_le_capacity
import Theorems.Thm_ThreeSum_LightBalancedOffset_time_bound
import Theorems.Thm_ThreeSum_LightKaratsuba_time_bound
import Theorems.Thm_ThreeSum_LightResidueHistogram_time_bound


set_option autoImplicit false
open ThreeSum ThreeSum.LightOriginalOffset
open Light LightResidues LightResidueHistogram
open KaratsubaInterface CyclicFold
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 8000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightOriginalOffset
theorem _root_.solution (p nLeft nRight U : ℕ) :
    time p nLeft nRight U ≤ LightKaratsuba.time (Nat.clog 2 p)+252*capacity p+
      131*(nLeft+nRight)*(Nat.log 2 (U+1)+1)+12*Nat.clog 2 p+642 := by
  have hL := LightResidueHistogram.time_bound nLeft (capacity p) U
  have hR := LightResidueHistogram.time_bound nRight (capacity p) U
  have hM := LightBalancedOffset.time_bound (Nat.clog 2 p) p (le_capacity p)
  change LightBalancedOffset.time (Nat.clog 2 p) p ≤
    LightKaratsuba.time (Nat.clog 2 p)+226*capacity p+226 at hM
  calc
    time p nLeft nRight U ≤ LightCapacity.time p+
        (13*capacity p+131*nLeft*(Nat.log 2 (U+1)+1)+53)+
        (13*capacity p+131*nRight*(Nat.log 2 (U+1)+1)+53)+
        (LightKaratsuba.time (Nat.clog 2 p)+226*capacity p+226)+300 := by
      unfold time
      omega
    _ = _ := by unfold LightCapacity.time; ring
end ThreeSum.LightOriginalOffset
