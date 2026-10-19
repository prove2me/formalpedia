-- Prove2me | solution 1 for TwoDegenerateGraphs.exists_hammingRetention_outside_event
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:08.630233+00:00
-- url     : https://prove2.me/submissions/f3a99574-50f8-4ab3-93ad-3294cae23e93

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_hammingRetentionMeasure_isProbability

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution
    (dimension : ℕ)
    (event : Set (Set (Bool × HammingWord dimension)))
    (hsmall : (hammingRetentionMeasure dimension).real event < 1) :
    ∃ retained : Set (Bool × HammingWord dimension), retained ∉ event := by
  letI : MeasureTheory.IsProbabilityMeasure
      (hammingRetentionMeasure dimension) :=
    hammingRetentionMeasure_isProbability dimension
  by_contra hnone
  push Not at hnone
  have hevent : event = Set.univ := Set.eq_univ_of_forall hnone
  rw [hevent] at hsmall
  simp at hsmall
end TwoDegenerateGraphs
