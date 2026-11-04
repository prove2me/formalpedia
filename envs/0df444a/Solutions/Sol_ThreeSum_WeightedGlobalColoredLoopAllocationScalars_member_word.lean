-- Prove2me | solution 1 for ThreeSum.WeightedGlobalColoredLoopAllocationScalars.member_word
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T03:15:09.603182+00:00
-- url     : https://prove2.me/submissions/5d2e9793-ee60-4f53-88d0-efa35f8d66c2

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryColoredLoopAllocation
import Definitions.Def_Submission_Weighted_Global_TernaryColoredLoopAllocationScalars
import Theorems.Thm_ThreeSum_WeightedGlobalColoredLoopAllocationScalars_sum_word
import Theorems.Thm_ThreeSum_WeightedGlobalArenaScoreScan_KeepInputs_trans


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalColoredLoopAllocationScalars
open Light WeightedGlobalConcreteProfile WeightedGlobalColoredLoopSetup WeightedGlobalColoredLoopAllocation
open WeightedGlobalArenaPrefixFootprints WeightedGlobalLocalParameters WeightedGlobalArenaLayout
set_option maxHeartbeats 200000
set_option maxRecDepth 24000
variable {κ : ℕ}
namespace ThreeSum.WeightedGlobalColoredLoopAllocationScalars
theorem _root_.solution {lim : Limits} {depth : ℕ} (P : Profile κ) (n free : ℕ) (A B C : List ℤ)
    (hok : (WeightedGlobalArenaAllocationResources.need P.allocation n (n^κ)).Ok lim
      (input P n free A B C).free depth) :
    ∀z∈values P n, |(z : ℤ)|≤lim.word := by
  intro z hz
  have hh:=List.le_sum_of_mem hz
  have hw:=sum_word P n free A B C hok
  rw [abs_of_nonneg (by positivity)]
  exact (Int.ofNat_le.mpr hh).trans hw
end ThreeSum.WeightedGlobalColoredLoopAllocationScalars
