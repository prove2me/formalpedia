-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedEulerMetadata.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:15:05.974553+00:00
-- url     : https://prove2.me/submissions/4d95343a-26f3-4f69-a897-4a22a72b7181

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_PredecessorTable
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_EulerMetadata
import Theorems.Thm_ThreeSum_LightMaskBits_time_bound
import Theorems.Thm_ThreeSum_LightTernaryLookup_time_bound
import Theorems.Thm_ThreeSum_LightTernaryPass_time_bound
import Theorems.Thm_ThreeSum_LightTernaryRankTable_time_bound
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedPredecessorTable_time_bound
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedPredecessor_time_bound


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedEulerMetadata
open Light ThreeSum.LightSubsetAddress ThreeSum.LightWeightedPredecessor
set_option maxHeartbeats 3000000
set_option maxRecDepth 24000
variable {lim : Limits} {P : Program}
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedEulerMetadata
theorem _root_.solution (N L rows : ℕ) :
    time N L rows≤5000*(N+L+1)^3*(rows+1) := by
  have hc := LightWeightedPredecessorTable.time_bound N L rows
  have hsqr : N+L+1≤(N+L+1)^2 := le_self_pow (by omega) (by decide)
  have hsq : 1≤(N+L+1)^2 := by omega
  have hpad : 200≤1000*(N+L+1)^2*(rows+1) := by
    have hm := Nat.mul_le_mul_left (1000*(N+L+1)^2) (show 1≤rows+1 by omega)
    omega
  have hb : LightWeightedPredecessorTable.time N L rows+200≤
      5000*(N+L+1)^2*(rows+1) := by nlinarith only [hc,hpad]
  have hm := Nat.mul_le_mul_left N hb
  have hn : N+1≤N+L+1 := by omega
  have hmul := Nat.mul_le_mul_right (5000*(N+L+1)^2*(rows+1)) hn
  have hpositive : 20≤5000*(N+L+1)^2*(rows+1) := by omega
  unfold time
  calc
    _ ≤ N*(5000*(N+L+1)^2*(rows+1))+20 := Nat.add_le_add_right hm 20
    _ ≤ (N+1)*(5000*(N+L+1)^2*(rows+1)) := by nlinarith only [hpositive]
    _ ≤ (N+L+1)*(5000*(N+L+1)^2*(rows+1)) := hmul
    _ = _ := by ring
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedEulerMetadata
