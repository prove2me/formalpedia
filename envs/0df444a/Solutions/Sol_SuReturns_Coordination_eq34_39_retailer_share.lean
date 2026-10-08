-- Prove2me | solution 1 for SuReturns.Coordination.eq34_39_retailer_share
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T03:44:57.424186+00:00
-- url     : https://prove2.me/submissions/c3f40901-94b7-472d-8b72-9b8b02ebbe4e

import Mathlib
import Definitions.Def_SuReturns_Coordination_Model

open MeasureTheory ProbabilityTheory

open SuReturns.Coordination


theorem solution (ν D : Measure ℝ) [IsProbabilityMeasure ν] (c s φ w b l : ℝ)
    (hw : w = φ * c + (1 - φ) * SuReturns.PartialRefunds.reservationPrice ν s)
    (hb : b = φ * s + (1 - φ) * SuReturns.PartialRefunds.reservationPrice ν s)
    (hl : b - l = s) :
    ∀ q : ℝ, retailerDiffBuyback ν D w b l (SuReturns.PartialRefunds.reservationPrice ν s) q s =
      φ * chainProfit ν D c s (SuReturns.PartialRefunds.reservationPrice ν s) q s := by
  intro q
  have hprob : SuReturns.PartialRefunds.keepProb ν s + SuReturns.PartialRefunds.returnProb ν s = 1 := by
    unfold SuReturns.PartialRefunds.keepProb SuReturns.PartialRefunds.returnProb
    rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
    rw [← measure_union (Set.disjoint_left.mpr (by
      intro x hx hy
      exact (not_lt_of_ge (show s ≤ x from hx)) (show x < s from hy))) measurableSet_Iio]
    simp [Set.Ici_union_Iio]
  have hl' : l = b - s := by linarith
  unfold retailerDiffBuyback chainProfit
  rw [hl', hw, hb]
  have hk : SuReturns.PartialRefunds.keepProb ν s = 1 - SuReturns.PartialRefunds.returnProb ν s := by linarith
  rw [hk]
  ring



#print axioms solution
