-- Prove2me | solution 1 for ThreeSum.WeightedGlobalPairedNativeDrift.paired_native_drift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:26:47.825514+00:00
-- url     : https://prove2.me/submissions/f9f32cb3-3e0d-46fa-9a8f-d38b334a341f

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryOversizeOverhead
import Definitions.Def_Submission_ThreeSum_TernaryPairedRecurrence
import Definitions.Def_Submission_Weighted_Global_TernaryPairedNativeDrift
import Theorems.Thm_ThreeSum_WeightedGlobalPairedNativeDrift_native_power_lower
import Theorems.Thm_Light_MatAt_congr
import Theorems.Thm_Light_Seg_congr


set_option autoImplicit false
open ThreeSum ThreeSum.WeightedGlobalPairedNativeDrift
namespace ThreeSum.WeightedGlobalPairedNativeDrift
theorem _root_.solution (K M R S p F : ℕ)
    (hS : M≤S^K) (hp : M*R*S^2≤p^2) (hF : (9*F)^4≤M) :
    (9*F*M*R^K)^4*M^(4*K+3)≤(p^(2*K))^4 := by
  have hlower := native_power_lower K M R S p hS hp
  calc
    _ = (9*F)^4*M^(4*K+7)*R^(4*K) := by
      rw [mul_pow,mul_pow,←pow_mul,Nat.mul_comm K 4]
      have hm : M^4*M^(4*K+3)=M^(4*K+7) := by
        rw [←pow_add]
        congr 1
        omega
      calc
        _ = (9*F)^4*(M^4*M^(4*K+3))*R^(4*K) := by ring
        _ = _ := by rw [hm]
    _ ≤ M*M^(4*K+7)*R^(4*K) := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hF)
    _ = (M^(K+2)*R^K)^4 := by
      rw [mul_pow,←pow_mul,←pow_mul]
      have hm : M*M^(4*K+7)=M^((K+2)*4) := by
        rw [←pow_succ']
        congr 1
        ring
      rw [hm]
      congr 1
      congr 1
      ring
    _ ≤ _ := Nat.pow_le_pow_left hlower 4
end ThreeSum.WeightedGlobalPairedNativeDrift
