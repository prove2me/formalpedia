-- Prove2me | solution 1 for ThreeSum.WeightedEnumeration.visits_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:29:15.408267+00:00
-- url     : https://prove2.me/submissions/eae2faf4-0ba6-4905-a4bb-df5721463d3a

import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Range
import Mathlib.Tactic
import Definitions.Def_Submission_Weighted_Enumeration
import Theorems.Thm_ThreeSum_WeightedEnumeration_digitCost_zero
import Theorems.Thm_ThreeSum_WeightedEnumeration_digitCost_one
import Theorems.Thm_ThreeSum_WeightedEnumeration_digitCost_two
import Theorems.Thm_ThreeSum_WeightedEnumeration_mem_digits
import Theorems.Thm_ThreeSum_WeightedEnumeration_words_nonempty
import Theorems.Thm_ThreeSum_WeightedEnumeration_words_length_succ
attribute [local simp] ThreeSum.WeightedEnumeration.digitCost_zero
attribute [local simp] ThreeSum.WeightedEnumeration.digitCost_one
attribute [local simp] ThreeSum.WeightedEnumeration.digitCost_two
attribute [local simp] ThreeSum.WeightedEnumeration.mem_digits
namespace ThreeSum.WeightedEnumeration
private theorem sum_map_mono (l : List ℕ) (f g : ℕ → ℕ)
    (h : ∀ x ∈ l, f x ≤ g x) : (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.map_cons, List.sum_cons]
    exact Nat.add_le_add (h x (by simp)) (ih (fun y hy => h y (by simp [hy])))
private theorem sum_map_mul (l : List ℕ) (c : ℕ) (f : ℕ → ℕ) :
    (l.map (fun x => c * f x)).sum = c * (l.map f).sum := by
  induction l with
  | nil => simp
  | cons x xs ih => simp [ih, Nat.mul_add]
end ThreeSum.WeightedEnumeration
set_option autoImplicit false
open ThreeSum ThreeSum.WeightedEnumeration
namespace ThreeSum.WeightedEnumeration
theorem _root_.solution (n t : ℕ) : visits n t ≤ (n + 1) * (words n t).length := by
  induction n generalizing t with
  | zero => simp [visits, words]
  | succ n ih =>
    have hs := sum_map_mono (digits t)
      (fun d => visits n (t - digitCost d)) (fun d => (n + 1) * (words n (t - digitCost d)).length)
      (fun d _ => ih (t - digitCost d))
    rw [sum_map_mul] at hs
    rw [← words_length_succ] at hs
    have hp := words_nonempty (n + 1) t
    simp only [visits]
    nlinarith
end ThreeSum.WeightedEnumeration
