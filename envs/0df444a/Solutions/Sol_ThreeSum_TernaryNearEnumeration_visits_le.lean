-- Prove2me | solution 1 for ThreeSum.TernaryNearEnumeration.visits_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:06:23.612995+00:00
-- url     : https://prove2.me/submissions/81e06d7a-b964-492d-b9dc-1498d2c5d474

import Definitions.Def_Submission_ThreeSum_TernaryAddresses
import Definitions.Def_Submission_ThreeSum_TernaryNearEnumeration
import Theorems.Thm_ThreeSum_TernaryNearEnumeration_mem_digits
import Theorems.Thm_ThreeSum_TernaryNearEnumeration_words_nonempty
import Theorems.Thm_ThreeSum_TernaryNearEnumeration_codes_length
import Theorems.Thm_ThreeSum_TernaryAddresses_codes_length
import Theorems.Thm_ThreeSum_TernaryEnumeration_mem_digits
import Theorems.Thm_ThreeSum_TernaryEnumeration_words_nonempty
attribute [local simp] ThreeSum.TernaryAddresses.codes_length
attribute [local simp] ThreeSum.TernaryEnumeration.mem_digits


attribute [local simp] ThreeSum.TernaryNearEnumeration.mem_digits
attribute [local simp] ThreeSum.TernaryNearEnumeration.codes_length
namespace ThreeSum.TernaryNearEnumeration
open ThreeSum.TernaryAddresses
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
end ThreeSum.TernaryNearEnumeration
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryNearEnumeration
open ThreeSum.TernaryAddresses
namespace ThreeSum.TernaryNearEnumeration
theorem _root_.solution (qs : List ℕ) (D : ℕ) :
    visits qs D ≤ (qs.length+1)*(words qs D).length := by
  induction qs generalizing D with
  | nil => simp [visits,words]
  | cons q qs ih =>
    have hs := sum_map_mono (digits q D)
      (fun r => visits qs (D-(q-r)))
      (fun r => (qs.length+1)*(words qs (D-(q-r))).length)
      (fun r _ => ih (D-(q-r)))
    rw [sum_map_mul] at hs
    have hlen : (words (q::qs) D).length =
      ((digits q D).map fun r => (words qs (D-(q-r))).length).sum := by
      simp [words,List.length_flatMap]
    rw [← hlen] at hs
    have hp := words_nonempty (q::qs) D
    simp only [visits,List.length_cons]
    nlinarith
end ThreeSum.TernaryNearEnumeration
