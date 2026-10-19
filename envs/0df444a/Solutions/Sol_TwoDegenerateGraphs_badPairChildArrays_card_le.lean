-- Prove2me | solution 1 for TwoDegenerateGraphs.badPairChildArrays_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:07.571959+00:00
-- url     : https://prove2.me/submissions/ab39b1f8-c955-4f84-bf15-d20073689105

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_pairTypeCountProfile_card
import Theorems.Thm_TwoDegenerateGraphs_pairChildArraysOfRealizedProfile_card_le

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution
    {parentCount dimension : ℕ}
    (hparents : 2 ≤ parentCount)
    (hdimension : 0 < dimension)
    (parents : Fin parentCount → HammingWord dimension)
    (threshold : ℝ) :
    ((badPairChildArrays parents threshold).card : ℝ) ≤
      (((parentCount.choose 2 + 1) ^ (3 * dimension) : ℕ) : ℝ) *
        Real.exp
          ((parentCount.choose 2 : ℝ) * Real.log 2 *
            (dimension : ℝ) * threshold) := by
  classical
  let bound : ℝ :=
    Real.exp
      ((parentCount.choose 2 : ℝ) * Real.log 2 *
        (dimension : ℝ) * threshold)
  have hbound_nonneg : 0 ≤ bound := by
    dsimp [bound]
    exact (Real.exp_pos _).le
  have hmaps :
      ((badPairChildArrays parents threshold :
        Finset (PairLayer parentCount 1 → HammingWord dimension)) :
        Set (PairLayer parentCount 1 → HammingWord dimension)).MapsTo
        (pairChildCountProfile parents)
        (Finset.univ : Finset (PairTypeCountProfile parentCount dimension)) := by
    intro children _
    exact Finset.mem_univ _
  have hpartition := Finset.card_eq_sum_card_fiberwise hmaps
  have hfiber (profile : PairTypeCountProfile parentCount dimension) :
      (((badPairChildArrays parents threshold).filter
        (fun children => pairChildCountProfile parents children = profile)).card : ℝ) ≤
        bound := by
    by_cases hnonempty :
        ((badPairChildArrays parents threshold).filter
          (fun children =>
            pairChildCountProfile parents children = profile)).Nonempty
    · obtain ⟨children, hchildren⟩ := hnonempty
      have hparts := Finset.mem_filter.mp hchildren
      have hprofile : pairChildCountProfile parents children = profile :=
        hparts.2
      have hbad : pairChildArrayEntropy parents children ≤ threshold := by
        have hmembership :
            children ∈
              (Finset.univ.filter
                (fun candidate : PairLayer parentCount 1 →
                    HammingWord dimension =>
                  pairChildArrayEntropy parents candidate ≤ threshold)) := by
          simpa only [badPairChildArrays] using hparts.1
        exact (Finset.mem_filter.mp hmembership).2
      have hsubset :
          (badPairChildArrays parents threshold).filter
              (fun candidate =>
                pairChildCountProfile parents candidate = profile) ⊆
            pairChildArraysOfProfile parents profile := by
        intro candidate hcandidate
        have hcandidate_profile := (Finset.mem_filter.mp hcandidate).2
        unfold pairChildArraysOfProfile
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, hcandidate_profile⟩
      have hcard :
          (((badPairChildArrays parents threshold).filter
            (fun candidate =>
              pairChildCountProfile parents candidate = profile)).card : ℝ) ≤
            ((pairChildArraysOfProfile parents profile).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsubset
      have hrealized :
          ((pairChildArraysOfProfile parents profile).card : ℝ) ≤
            Real.exp
              ((parentCount.choose 2 : ℝ) * Real.log 2 *
                (∑ coordinate : Fin dimension,
                  pairCoordinateConditionalEntropy
                    parents children coordinate)) := by
        rw [← hprofile]
        exact pairChildArraysOfRealizedProfile_card_le
          hparents parents children
      have hdimension_real : 0 < (dimension : ℝ) := by
        exact_mod_cast hdimension
      have hsum :
          (∑ coordinate : Fin dimension,
            pairCoordinateConditionalEntropy parents children coordinate) ≤
              (dimension : ℝ) * threshold := by
        unfold pairChildArrayEntropy at hbad
        have hcleared := (div_le_iff₀ hdimension_real).mp hbad
        nlinarith
      have hcoefficient :
          0 ≤ (parentCount.choose 2 : ℝ) * Real.log 2 :=
        mul_nonneg (Nat.cast_nonneg _) log_two_pos.le
      have hexponential :
          Real.exp
              ((parentCount.choose 2 : ℝ) * Real.log 2 *
                (∑ coordinate : Fin dimension,
                  pairCoordinateConditionalEntropy
                    parents children coordinate)) ≤ bound := by
        dsimp [bound]
        apply Real.exp_le_exp.mpr
        nlinarith [mul_le_mul_of_nonneg_left hsum hcoefficient]
      exact hcard.trans (hrealized.trans hexponential)
    · have hempty :
          (badPairChildArrays parents threshold).filter
            (fun children =>
              pairChildCountProfile parents children = profile) = ∅ :=
          Finset.not_nonempty_iff_eq_empty.mp hnonempty
      simpa [hempty] using hbound_nonneg
  calc
    ((badPairChildArrays parents threshold).card : ℝ) =
        ∑ profile : PairTypeCountProfile parentCount dimension,
          (((badPairChildArrays parents threshold).filter
            (fun children =>
              pairChildCountProfile parents children = profile)).card : ℝ) := by
      exact_mod_cast hpartition
    _ ≤ ∑ _profile : PairTypeCountProfile parentCount dimension, bound := by
      exact Finset.sum_le_sum (fun profile _ => hfiber profile)
    _ = (((parentCount.choose 2 + 1) ^ (3 * dimension) : ℕ) : ℝ) *
          Real.exp
            ((parentCount.choose 2 : ℝ) * Real.log 2 *
              (dimension : ℝ) * threshold) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        pairTypeCountProfile_card]
end TwoDegenerateGraphs
