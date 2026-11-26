-- Prove2me | solution 1 for TunnellMap.isParkingFunction_of_indexed_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:19:21.101703+00:00
-- url     : https://prove2.me/submissions/cb6df769-29b8-4b18-82df-fcc4a9d74a28

import Definitions.Def_TunnellMap_MatchedOrder
import Definitions.Def_TunnellMap_ParkingRearrangement
import Theorems.Thm_TunnellMap_GloballyRanked_insertEquiv_at_left
import Theorems.Thm_TunnellMap_GloballyRanked_insertEquiv_symm_at_right
attribute [local simp] TunnellMap.GloballyRanked.insertEquiv_at_left
attribute [local simp] TunnellMap.GloballyRanked.insertEquiv_symm_at_right



set_option autoImplicit true
open TunnellMap
namespace TunnellMap
theorem _root_.solution (a : List ℕ)
    (hpos : ∀ x ∈ a, 0 < x)
    (hbound : ∀ i : Fin a.length, a.get i ≤ i.1 + 1) :
    IsParkingFunction a := by
  refine ⟨hpos, ?_⟩
  intro i
  let b := sortedCounts a
  have hperm : b.Perm a := by
    exact List.mergeSort_perm a (· ≤ ·)
  have hlen : b.length = a.length := hperm.length_eq
  have hsorted : b.Pairwise (· ≤ ·) := by
    exact List.pairwise_mergeSort' (· ≤ ·) a
  by_contra hnot
  have hbi : i.1 + 1 < b.get i := Nat.lt_of_not_ge hnot
  let p : ℕ → Bool := fun x => decide (x ≤ i.1 + 1)
  have htakeLen : (a.take (i.1 + 1)).length = i.1 + 1 := by
    rw [List.length_take]
    apply Nat.min_eq_left
    rw [← hlen]
    exact Nat.succ_le_iff.mpr i.2
  have htakeFilter : (a.take (i.1 + 1)).filter p = a.take (i.1 + 1) := by
    apply List.filter_eq_self.mpr
    intro x hx
    obtain ⟨j, hj, hx⟩ := List.mem_take_iff_getElem.mp hx
    have hjLen : j < a.length :=
      lt_of_lt_of_le hj (Nat.min_le_right _ _)
    have hjIndex : j + 1 ≤ i.1 + 1 := by
      have : j < i.1 + 1 := lt_of_lt_of_le hj (Nat.min_le_left _ _)
      omega
    have hxBound := (hbound ⟨j, hjLen⟩).trans hjIndex
    subst x
    simpa [p] using hxBound
  have htakeCount : (a.take (i.1 + 1)).countP p = i.1 + 1 := by
    rw [List.countP_eq_length_filter, htakeFilter, htakeLen]
  have hcountLower : i.1 + 1 ≤ a.countP p := by
    rw [← htakeCount]
    exact (List.take_sublist (i.1 + 1) a).countP_le
  have hdropFilter : (b.drop i.1).filter p = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro x hx
    have hdropEq : b.drop i.1 = b.get i :: b.drop (i.1 + 1) :=
      List.drop_eq_getElem_cons i.2
    have hdropPairwise := hsorted.drop (i := i.1)
    rw [hdropEq] at hx hdropPairwise
    rcases List.mem_cons.mp hx with hx | hx
    · subst x
      simpa [p] using hbi
    · have hheadLe : b.get i ≤ x :=
        (List.pairwise_cons.mp hdropPairwise).1 x hx
      have hxGt : i.1 + 1 < x := hbi.trans_le hheadLe
      simp [p, Nat.not_le.mpr hxGt]
  have hdropCount : (b.drop i.1).countP p = 0 := by
    rw [List.countP_eq_length_filter, hdropFilter]
    rfl
  have hcountUpper : b.countP p ≤ i.1 := by
    calc
      b.countP p =
          (b.take i.1).countP p + (b.drop i.1).countP p := by
            rw [← List.countP_append, List.take_append_drop]
      _ ≤ (b.take i.1).length + 0 :=
        Nat.add_le_add List.countP_le_length hdropCount.le
      _ = i.1 := by
        rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt i.2)]
        simp
  have hcountEq : b.countP p = a.countP p := hperm.countP_eq p
  omega
end TunnellMap
