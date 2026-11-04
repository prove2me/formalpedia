-- Prove2me | solution 1 for ThreeSum.WeightedGlobalPairedNativeDrift.native_power_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:15:39.115871+00:00
-- url     : https://prove2.me/submissions/9505ed39-396b-495b-be61-0c06337bca05

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryOversizeOverhead
import Definitions.Def_Submission_ThreeSum_TernaryPairedRecurrence
import Definitions.Def_Submission_Weighted_Global_TernaryPairedNativeDrift

set_option autoImplicit false
open ThreeSum ThreeSum.WeightedGlobalPairedNativeDrift
namespace ThreeSum.WeightedGlobalPairedNativeDrift
theorem _root_.solution (K M R S p : ℕ) (hS : M≤S^K)
    (hp : M*R*S^2≤p^2) :
    M^(K+2)*R^K≤p^(2*K) := by
  have hs2 := Nat.pow_le_pow_left hS 2
  have hpK := Nat.pow_le_pow_left hp K
  have he : (S^K)^2=(S^2)^K := by
    rw [←pow_mul,←pow_mul,Nat.mul_comm K 2]
  calc
    _ = (M^K*R^K)*M^2 := by rw [pow_add]; ring
    _ ≤ (M^K*R^K)*(S^K)^2 := Nat.mul_le_mul_left _ hs2
    _ = (M*R*S^2)^K := by rw [he,mul_pow,mul_pow]
    _ ≤ (p^2)^K := hpK
    _ = _ := by rw [←pow_mul]
end ThreeSum.WeightedGlobalPairedNativeDrift
