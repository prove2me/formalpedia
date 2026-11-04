-- Prove2me | solution 1 for ThreeSum.LightTernaryFrozenQuery.outside_near_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:32:34.53701+00:00
-- url     : https://prove2.me/submissions/abac4e5e-d7bd-4364-bf0b-897ffbbefde0

import Definitions.Def_Submission_ThreeSum_LightTernaryFrozenQueryMain
import Definitions.Def_Submission_ThreeSum_TernaryConvolution
import Definitions.Def_Submission_ThreeSum_LightTernaryFrozenQueryPhysical
import Theorems.Thm_ThreeSum_TernaryBank_mem_nearWords
import Theorems.Thm_ThreeSum_TernaryBank_rank_add_deficit
attribute [local simp] ThreeSum.TernaryBank.mem_nearWords



set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryFrozenQuery
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryFrozenQueryStages ThreeSum.TernaryCodeSemantics
set_option maxHeartbeats 5000000
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightTernaryFrozenQuery
theorem _root_.solution {N : ℕ} (Q R : TritWord N) (T : ℕ) (hQ : T<rank Q) :
    R∈ThreeSum.TernaryBank.nearWords Q (rank Q-(T+1)) ↔ Below R Q ∧ T<rank R := by
  rw [mem_nearWords]
  constructor
  · intro ⟨hbelow,hdef⟩
    have hsum := rank_add_deficit hbelow
    exact ⟨hbelow,by omega⟩
  · intro ⟨hbelow,hrank⟩
    have hsum := rank_add_deficit hbelow
    exact ⟨hbelow,by omega⟩
end ThreeSum.LightTernaryFrozenQuery
