-- Prove2me | solution 1 for RandomGradFree.Smooth.le_smoothing
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:35:10.035527+00:00
-- url     : https://prove2.me/submissions/14523800-6d33-4d9a-8576-1366f1685ee8

import Mathlib
import Definitions.Def_RandomGradFree_Shared_smoothing

open MeasureTheory ProbabilityTheory

namespace RandomGradFree.Smooth

theorem aux_lesm_integrable_id {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] :
    Integrable (fun u : E => u) (stdGaussian E) :=
  IsGaussian.integrable_id

end RandomGradFree.Smooth

open RandomGradFree.Smooth

theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f : E → ℝ) (hf : ConvexOn ℝ Set.univ f)
    (μ : ℝ) (hμ : 0 ≤ μ) (x : E)
    (hint : Integrable (fun u => f (x + μ • u)) (stdGaussian E)) :
    f x ≤ RandomGradFree.Shared.smoothing f μ x := by
  have hcont : ContinuousOn f Set.univ := hf.continuousOn isOpen_univ
  have hid : Integrable (fun u : E => u) (stdGaussian E) := aux_lesm_integrable_id
  have hg : Integrable (fun u : E => x + μ • u) (stdGaussian E) :=
    (integrable_const x).add (hid.smul μ)
  have hJ := hf.map_integral_le (μ := stdGaussian E) (f := fun u : E => x + μ • u) hcont
    isClosed_univ (Filter.Eventually.of_forall (fun _ => Set.mem_univ _)) hg hint
  have hmean : ∫ u, (x + μ • u) ∂(stdGaussian E) = x := by
    have hs : Integrable (fun u : E => μ • u) (stdGaussian E) := hid.smul μ
    rw [integral_add (integrable_const x) hs, integral_const, integral_smul,
      integral_id_stdGaussian]
    simp
  rw [hmean] at hJ
  simpa [RandomGradFree.Shared.smoothing] using hJ
