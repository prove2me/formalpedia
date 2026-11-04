-- Prove2me | solution 1 for ThreeSum.WeightedScore.score_eq_remaining_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:58:31.668569+00:00
-- url     : https://prove2.me/submissions/2d1f13ab-350d-465a-ae84-be787bd2cc0e

import Definitions.Def_Submission_ThreeSum_WeightedModuli
import Definitions.Def_Submission_ThreeSum_ModuloCounts
import Definitions.Def_Submission_ThreeSum_WeightedScore
import Theorems.Thm_ThreeSum_WeightedModuli_weighted_count_eq


set_option autoImplicit false
open ThreeSum ThreeSum.WeightedScore
open Finset Arithmetic ModuloCounts WeightedModuli
open scoped BigOperators
namespace ThreeSum.WeightedScore
theorem _root_.solution (primes : ℕ → ℕ) (s q nA nB nC : ℕ)
    (a b c : ℕ → ℤ)
    (hprime : ∀ i < s, Nat.Prime (primes i))
    (hinj : ∀ i < s, ∀ j < s, primes i = primes j → i = j) :
    score primes s q nA nB nC a b c = remaining primes s q nA nB nC a b c s := by
  have hcard : (auxiliarySet primes s).card = s := by
    unfold auxiliarySet
    rw [Finset.card_image_of_injOn]
    · exact card_range s
    · intro i hi j hj heq
      exact hinj i (mem_range.mp hi) j (mem_range.mp hj) heq
  have hpr : ∀ p ∈ auxiliarySet primes s, Nat.Prime p := by
    intro p hp
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hp
    exact hprime i (mem_range.mp hi)
  have hsum : (∑ p ∈ auxiliarySet primes s,
      modCount (triples nA nB nC) (difference a b c) (joint q p)) =
      corrections primes q nA nB nC a b c s := by
    unfold auxiliarySet corrections count
    rw [sum_image]
    intro i hi j hj heq
    exact hinj i (mem_range.mp hi) j (mem_range.mp hj) heq
  unfold score
  rw [weighted_count_eq _ _ _ hpr q, hcard, hsum]
  rfl
end ThreeSum.WeightedScore
