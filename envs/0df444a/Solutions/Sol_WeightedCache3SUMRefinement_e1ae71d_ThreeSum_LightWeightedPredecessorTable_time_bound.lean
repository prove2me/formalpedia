-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedPredecessorTable.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:12:10.144193+00:00
-- url     : https://prove2.me/submissions/7d769e28-086e-4889-ac19-5a62a40a81eb

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Predecessor
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_PredecessorTable
import Theorems.Thm_ThreeSum_LightMaskBits_time_bound
import Theorems.Thm_ThreeSum_LightTernaryCodes_digit_time_bound
import Theorems.Thm_ThreeSum_LightTernaryLookup_time_bound
import Theorems.Thm_ThreeSum_LightTernaryPass_time_bound
import Theorems.Thm_ThreeSum_LightTernaryRankTable_time_bound
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedPredecessor_time_bound


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedPredecessorTable
open Light ThreeSum.LightSubsetAddress ThreeSum.LightWeightedPredecessor
set_option maxHeartbeats 3000000
set_option maxRecDepth 24000
variable {lim : Limits} {P : Program}
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedPredecessorTable
theorem _root_.solution (N L n : ℕ) : time N L n≤4000*(N+L+1)^2*(n+1) := by
  have hp := LightWeightedPredecessor.time_bound N L
  have hd := LightTernaryCodes.digit_time_bound (2*N)
  have hsqr : N+L+1≤(N+L+1)^2 := le_self_pow (by omega) (by decide)
  have hsmall : 400*(2*N+1)+200≤1000*(N+L+1)^2 := by omega
  have hr : LightWeightedPredecessor.time N L+LightTernaryCodes.digitTime (2*N)+200≤
      4000*(N+L+1)^2 := by
    calc
      _ ≤ 3000*(N+L+1)^2+(400*(2*N+1)+200) := by omega
      _ ≤ 3000*(N+L+1)^2+1000*(N+L+1)^2 := Nat.add_le_add_left hsmall _
      _ = _ := by ring
  have hK : 1≤(N+L+1)^2 := by nlinarith
  have hm := Nat.mul_le_mul_left n hr
  unfold time
  nlinarith [hm,hK]
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedPredecessorTable
