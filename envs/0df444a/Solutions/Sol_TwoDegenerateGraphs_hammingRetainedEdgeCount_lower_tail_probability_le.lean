-- Prove2me | solution 1 for TwoDegenerateGraphs.hammingRetainedEdgeCount_lower_tail_probability_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:08.630233+00:00
-- url     : https://prove2.me/submissions/245457f3-60cc-4f5d-8e42-196a26a4f21e

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_hammingRetentionMeasure_isProbability
import Theorems.Thm_TwoDegenerateGraphs_hammingExpectedRetainedEdgeCount_eq
import Theorems.Thm_TwoDegenerateGraphs_hammingExpectedRetainedEdgeCount_pos
import Theorems.Thm_TwoDegenerateGraphs_hammingRetainedEdgeCount_deviation_probability_le

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
attribute [local instance] Classical.propDecidable
namespace TwoDegenerateGraphs
theorem _root_.solution
    (dimension radius : ℕ) :
    (hammingRetentionMeasure dimension).real
      {retained : Set (Bool × HammingWord dimension) |
        hammingRetainedEdgeCount dimension radius retained <
          hammingExpectedRetainedEdgeCount dimension radius / 2} ≤
      4 / hammingExpectedRetainedEdgeCount dimension radius +
        8 / (hammingRetentionProbability dimension *
          ((2 ^ dimension : ℕ) : ℝ)) := by
  letI : MeasureTheory.IsProbabilityMeasure
      (hammingRetentionMeasure dimension) :=
    hammingRetentionMeasure_isProbability dimension
  have hmean := hammingExpectedRetainedEdgeCount_pos dimension radius
  have hthreshold :
      0 < hammingExpectedRetainedEdgeCount dimension radius / 2 := by
    positivity
  have hchebyshev := hammingRetainedEdgeCount_deviation_probability_le
    dimension radius
    (hammingExpectedRetainedEdgeCount dimension radius / 2)
    hthreshold
  have hsubset :
      {retained : Set (Bool × HammingWord dimension) |
        hammingRetainedEdgeCount dimension radius retained <
          hammingExpectedRetainedEdgeCount dimension radius / 2} ⊆
      {retained : Set (Bool × HammingWord dimension) |
        hammingExpectedRetainedEdgeCount dimension radius / 2 ≤
          |hammingRetainedEdgeCount dimension radius retained -
            hammingExpectedRetainedEdgeCount dimension radius|} := by
    intro retained hretained
    change
      hammingExpectedRetainedEdgeCount dimension radius / 2 ≤
        |hammingRetainedEdgeCount dimension radius retained -
          hammingExpectedRetainedEdgeCount dimension radius|
    have habsolute := neg_le_abs
      (hammingRetainedEdgeCount dimension radius retained -
        hammingExpectedRetainedEdgeCount dimension radius)
    change
      hammingRetainedEdgeCount dimension radius retained <
        hammingExpectedRetainedEdgeCount dimension radius / 2 at hretained
    linarith
  have hdegree_positive :
      0 < ((∑ distance ∈ Finset.range (radius + 1),
        dimension.choose distance : ℕ) : ℝ) := by
    have hterm :
        1 ≤ ∑ distance ∈ Finset.range (radius + 1),
          dimension.choose distance := by
      have hzero := Finset.single_le_sum
        (s := Finset.range (radius + 1))
        (f := fun distance : ℕ => dimension.choose distance)
        (fun distance _ => Nat.zero_le _)
        (show 0 ∈ Finset.range (radius + 1) by simp)
      simpa using hzero
    exact_mod_cast (show 0 < ∑ distance ∈ Finset.range (radius + 1),
      dimension.choose distance by omega)
  have hprobability := hammingRetentionProbability_pos dimension
  have hwords : 0 < ((2 ^ dimension : ℕ) : ℝ) := by
    positivity
  calc
    (hammingRetentionMeasure dimension).real
      {retained : Set (Bool × HammingWord dimension) |
        hammingRetainedEdgeCount dimension radius retained <
          hammingExpectedRetainedEdgeCount dimension radius / 2} ≤
      (hammingRetentionMeasure dimension).real
      {retained : Set (Bool × HammingWord dimension) |
        hammingExpectedRetainedEdgeCount dimension radius / 2 ≤
          |hammingRetainedEdgeCount dimension radius retained -
            hammingExpectedRetainedEdgeCount dimension radius|} :=
        MeasureTheory.measureReal_mono hsubset
    _ ≤
      (hammingExpectedRetainedEdgeCount dimension radius +
        2 * hammingRetentionProbability dimension ^ 3 *
          ((2 ^ dimension : ℕ) : ℝ) *
          ((∑ distance ∈ Finset.range (radius + 1),
            dimension.choose distance : ℕ) : ℝ) ^ 2) /
        (hammingExpectedRetainedEdgeCount dimension radius / 2) ^ 2 :=
      hchebyshev
    _ = 4 / hammingExpectedRetainedEdgeCount dimension radius +
        8 / (hammingRetentionProbability dimension *
          ((2 ^ dimension : ℕ) : ℝ)) := by
      rw [hammingExpectedRetainedEdgeCount_eq]
      field_simp [hprobability.ne', hwords.ne', hdegree_positive.ne']
      ring
end TwoDegenerateGraphs
