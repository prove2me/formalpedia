-- Prove2me | solution 1 for RatingsAdvert.AdInterval.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T08:18:05.820202+00:00
-- url     : https://prove2.me/submissions/054dc70d-287c-4d79-8ef7-15505f5648b9

import Mathlib
import Definitions.Def_RatingsAdvert_AdInterval_Model
import Theorems.Thm_RatingsAdvert_AdInterval_lemma_1
import Theorems.Thm_RatingsAdvert_AdInterval_lemma_2
import Theorems.Thm_RatingsAdvert_AdInterval_lemma_2_sufficiency
import Theorems.Thm_RatingsAdvert_AdInterval_lemma_3
import Theorems.Thm_RatingsAdvert_AdInterval_root_unique

open RatingsAdvert.AdInterval

theorem solution (P : Params) (hS : P.Standing) (hI : P.Interior) :
    (∃ z p1 p2 : ℝ, IsPBEBench P z p1 p2) ∧ (∃ (z p1 : ℝ) (p2 : ℝ → ℝ), IsPBERev P z p1 p2) ∧
      (∃ (z p1 : ℝ) (p2 : ℝ → ℝ), IsPBEAR P z p1 p2) ∧
      ∀ (z0 p10 p20 zR p1R : ℝ) (p2R : ℝ → ℝ) (zA p1A : ℝ) (p2A : ℝ → ℝ),
        IsPBEBench P z0 p10 p20 → IsPBERev P zR p1R p2R → IsPBEAR P zA p1A p2A →
        zR = z0 ∧ zA < z0 ∧ p1R = p10 ∧ p10 < p1A ∧
          (∀ q ∈ Set.Icc (0 : ℝ) 2, p2A q = p2R q) ∧ StrictMonoOn p2R (Set.Icc (0 : ℝ) 2) ∧
          p20 < p10 := by
  obtain ⟨⟨z7, hz7, -⟩, -, ⟨z8, hz8, -⟩, -⟩ := root_unique P hS hI
  have L1 := lemma_1 P hS hI
  have L3 := lemma_3 P hS hI
  refine ⟨⟨_, _, _, L1.2 z7 hz7.1 hz7.2⟩, ⟨_, _, _, L3.2 z7 hz7.1 hz7.2⟩,
    ⟨_, _, _, lemma_2_sufficiency P hS hI z8 hz8.1 hz8.2⟩, ?_⟩
  intro z0 p10 p20 zR p1R p2R zA p1A p2A hB hR hA
  obtain ⟨b1, b2, b3, -⟩ := L1.1 z0 p10 p20 hB
  obtain ⟨-, -, r3, -, r5, r6⟩ := L3.1 zR p1R p2R hR
  obtain ⟨-, -, a3, -, -⟩ := lemma_2 P hS hI zA p1A p2A hA
  obtain ⟨e1, e2⟩ := r5 z0 p10 p20 hB
  obtain ⟨f1, f2⟩ := r6 zA p1A p2A hA
  have hb : 0 < P.beta := hS.2.2.1
  have ht : 0 < P.tau := hS.1
  refine ⟨e1, e1 ▸ f1, e2, e2 ▸ f2, fun q hq => by rw [a3 q hq, r3 q hq], ?_, ?_⟩
  · intro x hx y hy hxy
    rw [r3 x hx, r3 y hy]
    have := mul_lt_mul_of_pos_left hxy hb
    linarith
  · rw [b2, b3]
    have := mul_lt_mul_of_pos_right b1.2 ht
    linarith
