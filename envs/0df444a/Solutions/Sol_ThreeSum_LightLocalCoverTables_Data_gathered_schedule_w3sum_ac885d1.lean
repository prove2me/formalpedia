-- Prove2me | solution 1 for ThreeSum.LightLocalCoverTables.Data.gathered_schedule_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:55:29.245248+00:00
-- url     : https://prove2.me/submissions/16630078-584b-4fe0-9241-146e6b195b3a

import Definitions.Def_Submission_ThreeSum_LightLocalCoverMatrix
import Definitions.Def_Submission_ThreeSum_LightLocalCoverSchedule
import Definitions.Def_Submission_ThreeSum_BlockCoefficientRows
import Definitions.Def_Submission_ThreeSum_LightLocalCoverTables
import Theorems.Thm_ThreeSum_BlockCoefficientRows_mapRow_fin
import Theorems.Thm_ThreeSum_LightLocalCoverSchedule_candidateAt_lt
import Theorems.Thm_ThreeSum_LightLocalCoverSchedule_candidateAt_mapAt
import Theorems.Thm_ThreeSum_LightWeightDecode_Rows_decodedWeight
attribute [local simp] ThreeSum.BlockCoefficientRows.mapRow_fin



set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalCoverTables
open Light LocalHashMoments LocalCoverBounds GlobalEncoding LightLocalCoverSchedule
namespace ThreeSum.LightLocalCoverTables
namespace Data
theorem _root_.solution {μ ν : ℕ → ℤ} {h maps hist0 hist1 matrixPtr dst : ℕ}
    (H : Data μ h maps hist0 hist1 matrixPtr)
    (hcopy : ∀ s < scheduleSize h, ∀ a < 2*(512*h),
      ν (dst+s*(2*(512*h))+a) = μ (maps+(indices h).getD s 0*(2*(512*h))+a)) :
    ScheduleRows ν h dst := by
  intro s hs i hi
  let o : Occurrence h := ⟨s,hs⟩
  have hc := ((H (candidateAt h o) (candidateAt_lt h o)).1).decodedWeight ⟨i,hi⟩
  change
    μ (maps+candidateAt h o*(2*(512*h))+i) = ((candidate h (candidateAt h o) (⟨i,hi⟩,false)).val : ℤ) ∧
    μ (maps+candidateAt h o*(2*(512*h))+512*h+i) = ((candidate h (candidateAt h o) (⟨i,hi⟩,true)).val : ℤ) at hc
  rw [candidateAt_mapAt h o] at hc
  rw [BlockCoefficientRows.mapRow_fin false o ⟨i,hi⟩,
    BlockCoefficientRows.mapRow_fin true o ⟨i,hi⟩]
  constructor
  · rw [hcopy s hs i (by omega)]
    exact hc.1
  · have he := hcopy s hs (512*h+i) (by omega)
    rw [← Nat.add_assoc,← Nat.add_assoc] at he
    rw [he]
    exact hc.2
end Data
end ThreeSum.LightLocalCoverTables
