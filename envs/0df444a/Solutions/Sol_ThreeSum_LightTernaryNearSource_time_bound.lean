-- Prove2me | solution 1 for ThreeSum.LightTernaryNearSource.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:20:07.724194+00:00
-- url     : https://prove2.me/submissions/209c2cc5-3792-4e4e-a3a1-d4191fb9d273

import Definitions.Def_Submission_ThreeSum_TernaryPhysicalEuler
import Definitions.Def_Submission_ThreeSum_LightTernaryNearSource
import Theorems.Thm_ThreeSum_LightMaskBits_time_bound
import Theorems.Thm_ThreeSum_LightTernaryDivide_time_bound
import Theorems.Thm_ThreeSum_LightTernaryEulerMemo_time_bound
import Theorems.Thm_ThreeSum_LightTernaryEulerMetadata_time_bound
import Theorems.Thm_ThreeSum_LightTernaryEulerRow_time_bound
import Theorems.Thm_ThreeSum_LightTernaryLookup_time_bound
import Theorems.Thm_ThreeSum_LightTernaryPass_time_bound
import Theorems.Thm_ThreeSum_LightTernaryPredecessorTable_time_bound
import Theorems.Thm_ThreeSum_LightTernaryPredecessor_time_bound
import Theorems.Thm_ThreeSum_LightTernaryRankTable_time_bound


set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryNearSource
open Light ThreeSum.LightSubsetAddress
open ThreeSum.LightTernaryEulerMetadata
set_option maxHeartbeats 4000000
set_option maxRecDepth 12000
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightTernaryNearSource
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
  have hMeta := LightTernaryEulerMetadata.time_bound N L rows
  have hMemo := LightTernaryEulerMemo.time_bound N rows stages V
  have hr : LightTernaryRankTable.time N rows≤2000*K^3*(rows+1) := by
    calc
      _≤2000*(N+1)^2*(rows+1) := hRank
      _≤2000*K^2*(rows+1) := by gcongr
      _≤2000*K^3*(rows+1) := by gcongr
  have hm : LightTernaryEulerMetadata.time N L rows≤5000*K^3*(rows+1) := by
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
end ThreeSum.LightTernaryNearSource
