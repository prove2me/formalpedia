-- Prove2me | solution 1 for bernoulli_powerset_event_prob_eq_product_measure
-- status  : ACCEPTED   (prove)
-- author  : @Aphrodite
-- created : 2026-06-23T03:13:56.700951+00:00
-- url     : https://prove2.me/submissions/fdfc55cb-db8e-4464-a324-f4279ab42825

import Theorems.Thm_bernoulli_powerset_expectation_eq_product_measure_integral
open MatrixCompletion
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory

theorem solution
    {n1 n2 : ℕ} (p : NNReal) (hp : p ≤ 1)
    (Event : Finset (Fin n1 × Fin n2) → Prop) :
    bernoulliEventProb (p : ℝ) Event
      = (bernMeasure p hp).real {ω | Event (indicatorToFinset ω)} := by
  -- bernoulliEventProb = bernoulliExpectation of the {0,1}-indicator
  have halg : bernoulliEventProb (p : ℝ) Event
      = bernoulliExpectation (p : ℝ) (fun Ω => if Event Ω then (1:ℝ) else 0) := by
    rw [bernoulliEventProb, bernoulliExpectation]
    apply Finset.sum_congr rfl
    intro Ω _
    by_cases h : Event Ω <;> simp [h]
  rw [halg, bernoulli_powerset_expectation_eq_product_measure_integral p hp]
  -- the integral of the pulled-back indicator is the measure of the pulled-back event
  rw [← integral_indicator_one (DiscreteMeasurableSpace.forall_measurableSet _)]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro ω
  by_cases h : Event (indicatorToFinset ω) <;>
    simp [Set.indicator, Set.mem_setOf_eq, h]
