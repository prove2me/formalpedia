-- Prove2me | solution 1 for SuReturns.Coordination.sec53_total_profit
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T02:07:34.753971+00:00
-- url     : https://prove2.me/submissions/8847de79-5dd9-4e3e-82f0-24d060fecdd1

import Mathlib
import Definitions.Def_SuReturns_Coordination_Model

open MeasureTheory ProbabilityTheory

open SuReturns.Coordination

theorem solution (ν D : Measure ℝ) [IsProbabilityMeasure ν] (c s w b : ℝ) :
    ∀ p q r : ℝ, retailerDirect ν D w b p q r + manufacturerDirect ν D c s w b p q r =
      chainProfit ν D c s p q r := by
  intro p q r
  have hprob : SuReturns.PartialRefunds.keepProb ν r + SuReturns.PartialRefunds.returnProb ν r = 1 := by
    unfold SuReturns.PartialRefunds.keepProb SuReturns.PartialRefunds.returnProb
    rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
    rw [← measure_union (Set.disjoint_left.mpr (by
      intro x hx hy
      exact (not_lt_of_ge (show r ≤ x from hx)) (show x < r from hy))) measurableSet_Iio]
    simp [Set.Ici_union_Iio]
  unfold retailerDirect manufacturerDirect chainProfit
  have hk : SuReturns.PartialRefunds.keepProb ν r = 1 - SuReturns.PartialRefunds.returnProb ν r := by linarith
  rw [hk]
  ring



#print axioms solution
