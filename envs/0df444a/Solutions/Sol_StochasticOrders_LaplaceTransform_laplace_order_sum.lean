-- Prove2me | solution 1 for StochasticOrders.LaplaceTransform.laplace_order_sum
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-25T05:21:30.003184+00:00
-- url     : https://prove2.me/submissions/4e0b859c-7a75-4c85-9796-32035393769d

import Mathlib
import Definitions.Def_StochasticOrders_LaplaceTransform_LaplaceOrder

set_option autoImplicit false

open MeasureTheory ProbabilityTheory StochasticOrders.LaplaceTransform in
theorem solution {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {m : ℕ} (X : Fin m → Ω → ℝ) (Y : Fin m → Ω' → ℝ) (hX : ∀ i, Measurable (X i))
    (hY : ∀ i, Measurable (Y i)) (hXnn : ∀ i ω, 0 ≤ X i ω) (hYnn : ∀ i ω, 0 ≤ Y i ω)
    (hXindep : iIndepFun X μ) (hYindep : iIndepFun Y ν)
    (hord : ∀ i, LaplaceOrder μ ν (X i) (Y i)) :
    LaplaceOrder μ ν (fun ω => ∑ i, X i ω) (fun ω => ∑ i, Y i ω) := by
  intro s hs
  have key : ∀ (Z : Fin m → ℝ),
      Real.exp (-(s * ∑ i, Z i)) = ∏ i, Real.exp (-(s * Z i)) := by
    intro Z
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib, Real.exp_sum]
  have hmf : Measurable (fun x : ℝ => Real.exp (-(s * x))) := by fun_prop
  have eX : ∫ ω, Real.exp (-(s * ∑ i, X i ω)) ∂μ = ∏ i, ∫ ω, Real.exp (-(s * X i ω)) ∂μ := by
    simp_rw [key]
    exact hXindep.integral_fun_prod_comp (f := fun _ x => Real.exp (-(s * x)))
      (fun i => (hX i).aemeasurable) (fun _ => hmf.aestronglyMeasurable)
  have eY : ∫ ω, Real.exp (-(s * ∑ i, Y i ω)) ∂ν = ∏ i, ∫ ω, Real.exp (-(s * Y i ω)) ∂ν := by
    simp_rw [key]
    exact hYindep.integral_fun_prod_comp (f := fun _ x => Real.exp (-(s * x)))
      (fun i => (hY i).aemeasurable) (fun _ => hmf.aestronglyMeasurable)
  show ∫ ω, Real.exp (-(s * ∑ i, X i ω)) ∂μ ≥ ∫ ω, Real.exp (-(s * ∑ i, Y i ω)) ∂ν
  rw [eX, eY]
  exact Finset.prod_le_prod (fun i _ => integral_nonneg fun ω => (Real.exp_pos _).le)
    (fun i _ => hord i s hs)
