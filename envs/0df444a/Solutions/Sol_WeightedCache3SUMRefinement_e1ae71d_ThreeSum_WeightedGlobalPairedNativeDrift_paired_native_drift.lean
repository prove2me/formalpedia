-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPairedNativeDrift.paired_native_drift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T11:25:15.960147+00:00
-- url     : https://prove2.me/submissions/443de079-b9b1-4b9d-8fd3-289dbe86b13c

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryOversizeOverhead
import Definitions.Def_Submission_ThreeSum_TernaryPairedRecurrence
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPairedNativeDrift
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalPairedNativeDrift_native_power_lower
import Theorems.Thm_Light_MatAt_congr
import Theorems.Thm_Light_Seg_congr


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPairedNativeDrift
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPairedNativeDrift
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
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPairedNativeDrift
