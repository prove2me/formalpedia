-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedEnumeration.mem_words
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:09:15.055622+00:00
-- url     : https://prove2.me/submissions/a7b99cf8-0f01-4c7d-aa64-2aeb21b668ec

import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Range
import Mathlib.Tactic
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Enumeration
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedEnumeration_digitCost_zero
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedEnumeration_digitCost_one
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedEnumeration_digitCost_two
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedEnumeration_mem_digits
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedEnumeration.digitCost_zero
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedEnumeration.digitCost_one
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedEnumeration.digitCost_two
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedEnumeration.mem_digits

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedEnumeration
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedEnumeration
theorem _root_.solution (n t : ℕ) (xs : List ℕ) :
    xs ∈ words n t ↔ xs.length = n ∧ (∀ d ∈ xs, d < 3) ∧ (xs.map digitCost).sum ≤ t := by
  induction n generalizing t xs with
  | zero =>
    simp only [words, List.mem_singleton]
    constructor
    · rintro rfl
      simp
    · rintro ⟨h, _, _⟩
      exact List.length_eq_zero_iff.mp h
  | succ n ih =>
    cases xs with
    | nil => simp [words]
    | cons d xs =>
      simp only [words, List.mem_flatMap, List.mem_map]
      constructor
      · rintro ⟨e, he, ys, hy, heq⟩
        have heq' : e = d ∧ ys = xs := List.cons.inj heq
        rcases heq' with ⟨rfl, rfl⟩
        obtain ⟨hd, hdt⟩ := mem_digits.mp he
        obtain ⟨hlen, hall, hsum⟩ := (ih (t - digitCost e) ys).mp hy
        refine ⟨by simp [hlen], ?_, ?_⟩
        · intro e he
          rcases List.mem_cons.mp he with rfl | he
          · exact hd
          · exact hall e he
        · simp only [List.map_cons, List.sum_cons]
          omega
      · rintro ⟨hlen, hall, hsum⟩
        have hd : d < 3 := hall d (by simp)
        have hdt : digitCost d ≤ t := by simp only [List.map_cons, List.sum_cons] at hsum; omega
        have htail : xs ∈ words n (t - digitCost d) := by
          apply (ih (t - digitCost d) xs).mpr
          refine ⟨by simpa using hlen, ?_, ?_⟩
          · intro e he
            exact hall e (by simp [he])
          · simp only [List.map_cons, List.sum_cons] at hsum
            omega
        exact ⟨d, mem_digits.mpr ⟨hd, hdt⟩, xs, htail, rfl⟩
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedEnumeration
