-- Prove2me | solution 1 for TunnellMap.GloballyRanked.proposalCount_total_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:02:18.795919+00:00
-- url     : https://prove2.me/submissions/c399fbbf-8c72-4cd4-bccc-68d7b64021c7

import Definitions.Def_TunnellMap_Parking
import Definitions.Def_TunnellMap_ParkingTotal
import Theorems.Thm_TunnellMap_sum_range_add_one_mul_two
import Theorems.Thm_TunnellMap_GloballyRanked_insertEquiv_at_left
import Theorems.Thm_TunnellMap_GloballyRanked_insertEquiv_symm_at_right
import Theorems.Thm_TunnellMap_GloballyRanked_proposalCount_le_position
attribute [local simp] TunnellMap.GloballyRanked.insertEquiv_at_left
attribute [local simp] TunnellMap.GloballyRanked.insertEquiv_symm_at_right



set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*} [LinearOrder K] [Fintype S] [Fintype T]
  [DecidableEq S] [DecidableEq T]
namespace TunnellMap.GloballyRanked
theorem _root_.solution (I : GloballyRanked K S T)
    (M : S ≃ T) (hM : I.Stable M)
    (order : Fin (Fintype.card S) ≃ S) (horder : I.MatchedKeyOrder M order) :
    (∑ s : S, I.proposalCount M s) ≤
      Fintype.card S * (Fintype.card S + 1) / 2 := by
  let m := Fintype.card S
  have hreindex : (∑ i : Fin m, I.proposalCount M (order i)) =
      ∑ s : S, I.proposalCount M s := order.sum_comp _
  have hpoint : (∑ i : Fin m, I.proposalCount M (order i)) ≤
      ∑ i : Fin m, (i.1 + 1) := by
    exact Finset.sum_le_sum fun i _ => I.proposalCount_le_position M hM order horder i
  have htri : (∑ i : Fin m, (i.1 + 1)) * 2 = m * (m + 1) := by
    have hfinrange : (∑ i : Fin m, (i.1 + 1)) =
        Finset.sum (Finset.range m) (fun i => i + 1) := by
      rw [Finset.sum_fin_eq_sum_range]
      apply Finset.sum_congr rfl
      intro i hi
      simp [Finset.mem_range.mp hi]
    rw [hfinrange]
    exact sum_range_add_one_mul_two m
  rw [← hreindex, Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
  calc
    (∑ i : Fin m, I.proposalCount M (order i)) * 2 ≤
        (∑ i : Fin m, (i.1 + 1)) * 2 := Nat.mul_le_mul_right 2 hpoint
    _ = m * (m + 1) := htri
end TunnellMap.GloballyRanked
