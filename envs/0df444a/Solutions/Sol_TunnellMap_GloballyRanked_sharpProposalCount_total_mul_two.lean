-- Prove2me | solution 1 for TunnellMap.GloballyRanked.sharpProposalCount_total_mul_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:19:52.394658+00:00
-- url     : https://prove2.me/submissions/5c28b73a-af9d-4a37-9868-56700b7c8b4a

import Definitions.Def_TunnellMap_ParkingRearrangement
import Definitions.Def_TunnellMap_Sharpness
import Theorems.Thm_TunnellMap_GloballyRanked_sharpProposalCount
import Theorems.Thm_TunnellMap_GloballyRanked_insertEquiv_at_left
import Theorems.Thm_TunnellMap_GloballyRanked_insertEquiv_symm_at_right
import Theorems.Thm_TunnellMap_GloballyRanked_length_matchedProposalCounts
import Theorems.Thm_TunnellMap_sum_range_add_one_mul_two
attribute [local simp] TunnellMap.GloballyRanked.insertEquiv_at_left
attribute [local simp] TunnellMap.GloballyRanked.insertEquiv_symm_at_right
attribute [local simp] TunnellMap.GloballyRanked.length_matchedProposalCounts



set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
namespace TunnellMap.GloballyRanked
theorem _root_.solution (m : ℕ) :
    (∑ i : Fin m,
      (sharpRanking m).proposalCount (sharpMatching m) i) * 2 =
        m * (m + 1) := by
  have hsum : (∑ i : Fin m,
      (sharpRanking m).proposalCount (sharpMatching m) i) =
      ∑ i : Fin m, (i.1 + 1) := by
    apply Finset.sum_congr rfl
    intro i _
    exact sharpProposalCount m i
  rw [hsum]
  have hfinrange : (∑ i : Fin m, (i.1 + 1)) =
      Finset.sum (Finset.range m) (fun i => i + 1) := by
    rw [Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i hi
    simp [Finset.mem_range.mp hi]
  rw [hfinrange]
  exact sum_range_add_one_mul_two m
end TunnellMap.GloballyRanked
