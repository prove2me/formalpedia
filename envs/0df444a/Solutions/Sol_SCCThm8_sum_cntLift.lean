-- Prove2me | solution 1 for SCCThm8.sum_cntLift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:57:02.905233+00:00
-- url     : https://prove2.me/submissions/b510a0f6-ba6f-4361-b30d-04b893590a66

module
public import Definitions.Def_SCCThm8_Defs
public import Definitions.Def_SCCThm8_Counting
public import Theorems.Thm_SCCThm8_sum_cntRank

set_option autoImplicit true
@[expose] public section
public section
open SCCThm8
open Finset
namespace SCCThm8
theorem _root_.solution {n : ℕ} (v : Finset (Fin n)) (hv : Even v.card) :
    ∑ i, cntLift v i = 0 := by
  have h : ∑ i, cntLift v i =
      ∑ i ∈ v, (fun r => if 2 * r < v.card then (1 : ℤ) else -1) (cntRank v i) := by
    rw [← sum_subset (subset_univ v)]
    · exact sum_congr rfl fun i hi => by simp [cntLift, hi]
    · intro i _ hi
      simp [cntLift, hi]
  rw [h]
  refine (sum_cntRank (fun r => if 2 * r < v.card then (1 : ℤ) else -1) v).trans ?_
  obtain ⟨k, hk⟩ := hv
  rw [hk, sum_range_add]
  have e1 : ∑ x ∈ range k, (if 2 * x < k + k then (1 : ℤ) else -1) = ∑ x ∈ range k, (1 : ℤ) :=
    sum_congr rfl fun x hx => by rw [mem_range] at hx; rw [if_pos (by omega)]
  have e2 : ∑ x ∈ range k, (if 2 * (k + x) < k + k then (1 : ℤ) else -1) =
      ∑ x ∈ range k, (-1 : ℤ) :=
    sum_congr rfl fun x _ => by rw [if_neg (by omega)]
  rw [e1, e2]
  simp
end SCCThm8
