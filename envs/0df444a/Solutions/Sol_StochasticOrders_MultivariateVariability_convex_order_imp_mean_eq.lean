-- Prove2me | solution 1 for StochasticOrders.MultivariateVariability.convex_order_imp_mean_eq
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T19:59:01.387371+00:00
-- url     : https://prove2.me/submissions/6238b274-4bfa-46b6-ae94-071e8c954984

import Mathlib
import Definitions.Def_StochasticOrders_MultivariateVariability_ConvexOrder

set_option autoImplicit false

open MeasureTheory StochasticOrders.MultivariateVariability in
theorem solution {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {n : ℕ} (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (X : Ω → Fin n → ℝ) (Y : Ω' → Fin n → ℝ) (hX : Integrable X μ) (hY : Integrable Y ν)
    (hord : ConvexOrder μ ν X Y) :
    ∫ ω, X ω ∂μ = ∫ ω, Y ω ∂ν := by
  funext i
  have hXi : ∀ j, Integrable (fun ω => X ω j) μ := Integrable.eval hX
  have hYi : ∀ j, Integrable (fun ω => Y ω j) ν := Integrable.eval hY
  rw [eval_integral hXi i, eval_integral hYi i]
  let L : (Fin n → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj i
  have h1 := hord (fun v => v i) (L.convexOn convex_univ) (hXi i) (hYi i)
  have h2 := hord (fun v => -v i) ((-L).convexOn convex_univ) (hXi i).neg (hYi i).neg
  simp only [integral_neg] at h2
  exact le_antisymm h1 (neg_le_neg_iff.mp h2)
