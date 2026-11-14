-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.latent_mixture_marginal
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T06:40:33.755902+00:00
-- url     : https://prove2.me/submissions/ee70bb0b-0c34-4134-8a79-0f73af2bdc66

import Mathlib
set_option autoImplicit false
open scoped BigOperators
open MeasureTheory

theorem solution {ι X : Type} [Fintype ι] [MeasurableSpace X] (μ : Measure X)
    (A : ι → ℝ) (w : ι → X → ℝ)
    (hint : ∀ i, Integrable (w i) μ)
    (hmean : ∀ i, (∫ y, w i y ∂μ) = 1) (x : X) :
    (∫ y, ∑ i, A i * w i x * w i y ∂μ) = ∑ i, A i * w i x := by
  classical
  have hi (i : ι) : Integrable (fun y => A i*w i x*w i y) μ :=
    (hint i).const_mul (A i*w i x)
  rw [integral_finsetSum _ (fun i hi' => hi i)]
  apply Finset.sum_congr rfl
  intro i hi'
  rw [integral_const_mul, hmean]
  ring
