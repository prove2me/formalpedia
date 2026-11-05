-- Prove2me | solution 1 for TwoAgentSched.Shops.theorems_10_1_10_2
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T13:16:51.629995+00:00
-- url     : https://prove2.me/submissions/9f4818e0-c408-47e6-846c-dc18150d128e

import Mathlib
import Definitions.Def_TwoAgentSched_Shops_Model
import Definitions.Def_TwoAgentSched_Shops_Construction
import Theorems.Thm_TwoAgentSched_Shops_shops_encoding_reduction
import Theorems.Thm_TwoAgentSched_Shops_theorem_10_1_equivalence
import Theorems.Thm_TwoAgentSched_Shops_theorem_10_2_equivalence

open TwoAgentSched.Shops CookPvsNP ProjSchedTW.Complexity

private lemma fin_sum_get_eq_list_sum (s : List ℕ) :
    (∑ i : Fin s.length, s.get i) = s.sum := by
  induction s with
  | nil => rfl
  | cons a t ih =>
    rw [List.sum_cons, ← ih]
    exact Fin.sum_univ_succ (fun i : Fin (a :: t).length => (a :: t).get i)

private lemma partitionYes_even_sum (s : List ℕ) (h : PartitionYes s) : Even s.sum := by
  rcases h with ⟨A, hA⟩
  have htot : (∑ i ∈ A, s.get i) + (∑ i ∈ Aᶜ, s.get i) = s.sum := by
    rw [Finset.sum_add_sum_compl, fin_sum_get_eq_list_sum]
  exact ⟨∑ i ∈ A, s.get i, by omega⟩

private lemma partitionYes_of_sum_zero (s : List ℕ) (h : s.sum = 0) : PartitionYes s := by
  refine ⟨∅, ?_⟩
  have htot : (∑ i : Fin s.length, s.get i) = 0 := by
    rw [fin_sum_get_eq_list_sum, h]
  have h1 : (∑ i ∈ (∅ : Finset (Fin s.length)), s.get i) = 0 := Finset.sum_empty
  have h2 : (∑ i ∈ (∅ : Finset (Fin s.length))ᶜ, s.get i) = 0 := by
    rw [Finset.compl_empty, htot]
  rw [h1, h2]

theorem solution :
    PolyReducible partitionLang flowLang ∧ PolyReducible partitionLang openLang := by
  rcases shops_encoding_reduction with ⟨⟨f, hf_poly, hf_iff⟩, ⟨g, hg_poly, hg_iff⟩⟩
  refine ⟨⟨f, hf_poly, fun x => ?_⟩, ⟨g, hg_poly, fun x => ?_⟩⟩
  · rw [← hf_iff x]
    constructor
    · rintro ⟨p, hp, rfl⟩
      have heven : Even p.sum := partitionYes_even_sum p hp
      rcases heven with ⟨k, hk⟩
      by_cases hk0 : k = 0
      · exact Or.inr ⟨p, by omega, rfl⟩
      · have h2 : 2 ≤ p.sum := by omega
        exact Or.inl ⟨p, ⟨k, hk⟩, Or.inl h2,
          (theorem_10_1_equivalence p ⟨k, hk⟩ (Or.inl h2)).mp hp, rfl⟩
    · rintro (⟨p, heven, hrange, hflow, hx⟩ | ⟨p, h0, hx⟩)
      · exact ⟨p, (theorem_10_1_equivalence p heven hrange).mpr hflow, hx⟩
      · exact ⟨p, partitionYes_of_sum_zero p h0, hx⟩
  · rw [← hg_iff x]
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p, (theorem_10_2_equivalence p).mp hp, rfl⟩
    · rintro ⟨p, hopen, hx⟩
      exact ⟨p, (theorem_10_2_equivalence p).mpr hopen, hx⟩
