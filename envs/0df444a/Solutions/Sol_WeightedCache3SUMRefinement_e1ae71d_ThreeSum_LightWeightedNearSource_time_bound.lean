-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedNearSource.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:17:09.883003+00:00
-- url     : https://prove2.me/submissions/d21a2a43-c89b-435d-b30a-7e56b283f469

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_PhysicalEuler
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_NearSource
import Theorems.Thm_ThreeSum_LightMaskBits_time_bound
import Theorems.Thm_ThreeSum_LightTernaryDivide_time_bound
import Theorems.Thm_ThreeSum_LightTernaryEulerMemo_time_bound
import Theorems.Thm_ThreeSum_LightTernaryEulerRow_time_bound
import Theorems.Thm_ThreeSum_LightTernaryLookup_time_bound
import Theorems.Thm_ThreeSum_LightTernaryPass_time_bound
import Theorems.Thm_ThreeSum_LightTernaryRankTable_time_bound
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedEulerMetadata_time_bound
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedPredecessorTable_time_bound
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedPredecessor_time_bound


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedNearSource
open Light ThreeSum.LightSubsetAddress
open ThreeSum.LightWeightedEulerMetadata
set_option maxHeartbeats 4000000
set_option maxRecDepth 12000
variable {lim : Limits} {P : Program}
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedNearSource
theorem _root_.solution {N L rows stages V : ℕ} (hstages : stages≤2*N) :
    time N L rows stages V≤
      11000*(N+L+Nat.log 2 (V+1)+3)^3*(rows+1) := by
  let K := N+L+Nat.log 2 (V+1)+3
  have hK : 1≤K := by omega
  have hN : N+1≤K := by omega
  have hNL : N+L+1≤K := by omega
  have hNlog : N+Nat.log 2 (V+1)+3≤K := by omega
  have hpow : K^2≤K^3 := Nat.pow_le_pow_right hK (by decide)
  have hRank := LightTernaryRankTable.time_bound N rows
  have hMeta := LightWeightedEulerMetadata.time_bound N L rows
  have hMemo := LightTernaryEulerMemo.time_bound N rows stages V
  have hr : LightTernaryRankTable.time N rows≤2000*K^3*(rows+1) := by
    calc
      _≤2000*(N+1)^2*(rows+1) := hRank
      _≤2000*K^2*(rows+1) := by gcongr
      _≤2000*K^3*(rows+1) := by gcongr
  have hm : LightWeightedEulerMetadata.time N L rows≤5000*K^3*(rows+1) := by
    calc
      _≤5000*(N+L+1)^3*(rows+1) := hMeta
      _≤5000*K^3*(rows+1) := by gcongr
  have he : LightTernaryEulerMemo.time N rows stages V≤2700*K^3*(rows+1) := by
    have hs : stages+1≤3*K := by omega
    have ht : 400*(N+Nat.log 2 (V+1)+3)+500≤900*K := by omega
    calc
      _≤(stages+1)*(rows+1)*(400*(N+Nat.log 2 (V+1)+3)+500) := hMemo
      _≤(3*K)*(rows+1)*(900*K) := by gcongr
      _=2700*K^2*(rows+1) := by ring
      _≤2700*K^3*(rows+1) := by gcongr
  have hlarge : 1≤K^3*(rows+1) := by
    have hkpow : 1≤K^3 := one_le_pow₀ hK
    nlinarith
  unfold time
  change _≤11000*K^3*(rows+1)
  nlinarith only [hr,hm,he,hlarge]
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedNearSource
