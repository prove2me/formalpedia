-- Prove2me | solution 1 for StochasticOrders.Multivariate.multivariate_order_marginalization
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-25T05:05:01.229904+00:00
-- url     : https://prove2.me/submissions/615efff5-7bea-443a-9513-374b8e6c3bbd

import Mathlib
import Definitions.Def_StochasticOrders_Multivariate_MultivariateOrder

set_option autoImplicit false

open MeasureTheory ProbabilityTheory StochasticOrders.Multivariate in
theorem solution {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {n k : ℕ} (X : Ω → Fin n → ℝ) (Y : Ω' → Fin n → ℝ) (hord : MultivariateOrder μ ν X Y)
    (r : Fin k → Fin n) (hr : Function.Injective r) :
    MultivariateOrder μ ν (fun ω i => X ω (r i)) (fun ω i => Y ω (r i)) := by
  intro φ hφ hXi hYi
  have hψ : Monotone (fun x : Fin n → ℝ => φ (fun i => x (r i))) := by
    intro a b hab
    exact hφ (fun i => hab (r i))
  exact hord (fun x : Fin n → ℝ => φ (fun i => x (r i))) hψ hXi hYi
