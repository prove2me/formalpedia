-- Prove2me | solution 2 for TwoDegenerateGraphs.binomial_probability_term_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:05.132814+00:00
-- url     : https://prove2.me/submissions/f5f3c0c6-5326-4487-99a4-de06fc611bb7

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution
    (trialCount successCount : ℕ) (probability : ℝ)
    (hcount : successCount ≤ trialCount)
    (hprobability_zero : 0 ≤ probability)
    (hprobability_one : probability ≤ 1) :
    (trialCount.choose successCount : ℝ) *
        probability ^ successCount *
        (1 - probability) ^ (trialCount - successCount) ≤ 1 := by
  have hcomplement : 0 ≤ 1 - probability :=
    sub_nonneg.mpr hprobability_one
  have hsum :
      (∑ count ∈ Finset.range (trialCount + 1),
        probability ^ count *
          (1 - probability) ^ (trialCount - count) *
          (trialCount.choose count : ℝ)) = 1 := by
    calc
      (∑ count ∈ Finset.range (trialCount + 1),
          probability ^ count *
            (1 - probability) ^ (trialCount - count) *
            (trialCount.choose count : ℝ)) =
          (probability + (1 - probability)) ^ trialCount :=
        (add_pow probability (1 - probability) trialCount).symm
      _ = 1 := by
        rw [show probability + (1 - probability) = 1 by ring]
        simp
  have hterm := Finset.single_le_sum
    (s := Finset.range (trialCount + 1))
    (f := fun count : ℕ =>
      probability ^ count *
        (1 - probability) ^ (trialCount - count) *
        (trialCount.choose count : ℝ))
    (fun count _ => by positivity)
    (show successCount ∈ Finset.range (trialCount + 1) by
      simp; omega)
  rw [hsum] at hterm
  nlinarith
end TwoDegenerateGraphs
