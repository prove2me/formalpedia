-- Prove2me | solution 1 for TwoDegenerateGraphs.hammingRetainedVertexCount_upper_tail_probability_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:08.630233+00:00
-- url     : https://prove2.me/submissions/9d142205-f673-4a60-ba7c-535608803a6f

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_hammingRetentionMeasure_isProbability
import Theorems.Thm_TwoDegenerateGraphs_hammingExpectedRetainedVertexCount_eq
import Theorems.Thm_TwoDegenerateGraphs_hammingExpectedRetainedVertexCount_pos
import Theorems.Thm_TwoDegenerateGraphs_hammingRetainedVertexCount_deviation_probability_le

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution
    (dimension : ℕ) :
    (hammingRetentionMeasure dimension).real
      {retained : Set (Bool × HammingWord dimension) |
        3 * hammingRetentionProbability dimension *
            ((2 ^ dimension : ℕ) : ℝ) ≤
          hammingRetainedVertexCount dimension retained} ≤
      4 / hammingExpectedRetainedVertexCount dimension := by
  letI : MeasureTheory.IsProbabilityMeasure
      (hammingRetentionMeasure dimension) :=
    hammingRetentionMeasure_isProbability dimension
  have hmean := hammingExpectedRetainedVertexCount_pos dimension
  have hthreshold :
      0 < hammingExpectedRetainedVertexCount dimension / 2 := by
    positivity
  have hchebyshev := hammingRetainedVertexCount_deviation_probability_le
    dimension (hammingExpectedRetainedVertexCount dimension / 2)
    hthreshold
  have hsubset :
      {retained : Set (Bool × HammingWord dimension) |
        3 * hammingRetentionProbability dimension *
            ((2 ^ dimension : ℕ) : ℝ) ≤
          hammingRetainedVertexCount dimension retained} ⊆
      {retained : Set (Bool × HammingWord dimension) |
        hammingExpectedRetainedVertexCount dimension / 2 ≤
          |hammingRetainedVertexCount dimension retained -
            hammingExpectedRetainedVertexCount dimension|} := by
    intro retained hretained
    change
      hammingExpectedRetainedVertexCount dimension / 2 ≤
        |hammingRetainedVertexCount dimension retained -
          hammingExpectedRetainedVertexCount dimension|
    have habsolute := le_abs_self
      (hammingRetainedVertexCount dimension retained -
        hammingExpectedRetainedVertexCount dimension)
    rw [hammingExpectedRetainedVertexCount_eq] at habsolute ⊢
    change
      3 * hammingRetentionProbability dimension *
          ((2 ^ dimension : ℕ) : ℝ) ≤
        hammingRetainedVertexCount dimension retained at hretained
    nlinarith
  calc
    (hammingRetentionMeasure dimension).real
      {retained : Set (Bool × HammingWord dimension) |
        3 * hammingRetentionProbability dimension *
            ((2 ^ dimension : ℕ) : ℝ) ≤
          hammingRetainedVertexCount dimension retained} ≤
      (hammingRetentionMeasure dimension).real
        {retained : Set (Bool × HammingWord dimension) |
          hammingExpectedRetainedVertexCount dimension / 2 ≤
            |hammingRetainedVertexCount dimension retained -
              hammingExpectedRetainedVertexCount dimension|} :=
        MeasureTheory.measureReal_mono hsubset
    _ ≤ hammingExpectedRetainedVertexCount dimension /
        (hammingExpectedRetainedVertexCount dimension / 2) ^ 2 :=
      hchebyshev
    _ = 4 / hammingExpectedRetainedVertexCount dimension := by
      field_simp [hmean.ne']
      ring
end TwoDegenerateGraphs
