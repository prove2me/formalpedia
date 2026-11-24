-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_SmallRankBound_intersectionNumber_baseChange_63d64eced049
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:51:09.278878+00:00
-- url     : https://prove2.me/submissions/38dc58d1-e9b7-48ae-871e-bf2c599dbd33

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Elementary

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.RestTerms
open Finset
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace SmallRankBound
theorem _root_.solution : SmallRankBound.Statement := by
  intro k m j' N hm hk hj hN
  have h3 : 8 ≤ m ^ 3 := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ m ^ 3 := Nat.pow_le_pow_left hm 3
  have h4 : 8 * m ≤ m ^ 4 := by
    calc 8 * m ≤ m ^ 3 * m := Nat.mul_le_mul_right m h3
      _ = m ^ 4 := by ring
  have hk' : 2 * m + 2 ≤ k := by omega
  exact ⟨hk', by omega⟩
end SmallRankBound
end GroundTheory.Heights₂.Heights.RestTerms
