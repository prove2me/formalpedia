-- Prove2me | solution 1 for ThreeSum.WeightedNearEnumeration.visits_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:06:10.072592+00:00
-- url     : https://prove2.me/submissions/95f07ea9-9dcf-4478-9fc9-70c39cf39207

import Definitions.Def_Submission_Weighted_Addresses
import Definitions.Def_Submission_Weighted_NearEnumeration
import Theorems.Thm_ThreeSum_WeightedNearEnumeration_mem_digits
import Theorems.Thm_ThreeSum_WeightedNearEnumeration_words_nonempty
import Theorems.Thm_ThreeSum_WeightedNearEnumeration_codes_length
import Theorems.Thm_ThreeSum_TernaryAddresses_codes_length
import Theorems.Thm_ThreeSum_TernaryEnumeration_mem_digits
import Theorems.Thm_ThreeSum_TernaryEnumeration_words_nonempty
import Theorems.Thm_ThreeSum_WeightedAddresses_codes_length
import Theorems.Thm_ThreeSum_WeightedEnumeration_digitCost_one
import Theorems.Thm_ThreeSum_WeightedEnumeration_digitCost_two
import Theorems.Thm_ThreeSum_WeightedEnumeration_digitCost_zero
import Theorems.Thm_ThreeSum_WeightedEnumeration_mem_digits
import Theorems.Thm_ThreeSum_WeightedEnumeration_words_nonempty
attribute [local simp] ThreeSum.TernaryAddresses.codes_length
attribute [local simp] ThreeSum.TernaryEnumeration.mem_digits
attribute [local simp] ThreeSum.WeightedAddresses.codes_length
attribute [local simp] ThreeSum.WeightedEnumeration.digitCost_one
attribute [local simp] ThreeSum.WeightedEnumeration.digitCost_two
attribute [local simp] ThreeSum.WeightedEnumeration.digitCost_zero
attribute [local simp] ThreeSum.WeightedEnumeration.mem_digits


attribute [local simp] ThreeSum.WeightedNearEnumeration.mem_digits
attribute [local simp] ThreeSum.WeightedNearEnumeration.codes_length
namespace ThreeSum.WeightedNearEnumeration
open ThreeSum.WeightedAddresses ThreeSum.WeightedEnumeration
private theorem sum_map_mono (l : List ℕ) (f g : ℕ → ℕ)
    (h : ∀ x ∈ l, f x ≤ g x) : (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons,List.sum_cons]
    exact Nat.add_le_add (h x (by simp)) (ih (fun y hy => h y (by simp [hy])))
private theorem sum_map_mul (l : List ℕ) (c : ℕ) (f : ℕ → ℕ) :
    (l.map (fun x => c*f x)).sum = c*(l.map f).sum := by
  induction l with
  | nil => simp
  | cons x xs ih => simp [ih,Nat.mul_add]
end ThreeSum.WeightedNearEnumeration
set_option autoImplicit false
open ThreeSum ThreeSum.WeightedNearEnumeration
open ThreeSum.WeightedAddresses ThreeSum.WeightedEnumeration
namespace ThreeSum.WeightedNearEnumeration
theorem _root_.solution (qs : List ℕ) (D : ℕ) :
    visits qs D ≤ (qs.length+1)*(words qs D).length := by
  induction qs generalizing D with
  | nil => simp [visits,words]
  | cons q qs ih =>
    have hs := sum_map_mono (digits q D)
      (fun r => visits qs (D-(digitCost q-digitCost r)))
      (fun r => (qs.length+1)*(words qs (D-(digitCost q-digitCost r))).length)
      (fun r _ => ih (D-(digitCost q-digitCost r)))
    rw [sum_map_mul] at hs
    have hlen : (words (q::qs) D).length =
      ((digits q D).map fun r => (words qs (D-(digitCost q-digitCost r))).length).sum := by
      simp [words,List.length_flatMap]
    rw [← hlen] at hs
    have hp := words_nonempty (q::qs) D
    simp only [visits,List.length_cons]
    nlinarith
end ThreeSum.WeightedNearEnumeration
