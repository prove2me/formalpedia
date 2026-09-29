-- Prove2me | solution 1 for RandomGradFree.Nonsmooth.le_smoothing
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:14:07.426839+00:00
-- url     : https://prove2.me/submissions/42f1d594-8f07-405f-b8ee-78a43f3e5db7

import Mathlib
import Definitions.Def_RandomGradFree_Shared_smoothing

open MeasureTheory ProbabilityTheory

namespace RandomGradFree.Nonsmooth

end RandomGradFree.Nonsmooth

open RandomGradFree.Nonsmooth

theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f : E → ℝ) (hf : ConvexOn ℝ Set.univ f)
    (μ : ℝ) (hμ : 0 ≤ μ) (x : E)
    (hint : Integrable (fun u => f (x + μ • u)) (stdGaussian E)) :
    f x ≤ RandomGradFree.Shared.smoothing f μ x := by
  have hcont : ContinuousOn f Set.univ := hf.continuousOn isOpen_univ
  have hid : Integrable (fun u : E => u) (stdGaussian E) := IsGaussian.integrable_id
  have hsm : Integrable (fun u : E => μ • u) (stdGaussian E) := hid.smul μ
  have hg : Integrable (fun u : E => x + μ • u) (stdGaussian E) :=
    (integrable_const x).add hsm
  have hmean : ∫ u, (x + μ • u) ∂(stdGaussian E) = x := by
    rw [integral_add (integrable_const x) hsm, integral_const, integral_smul,
      integral_id_stdGaussian]
    simp
  have key := hf.map_integral_le (μ := stdGaussian E) (f := fun u : E => x + μ • u) hcont
    isClosed_univ (Filter.Eventually.of_forall (fun _ => Set.mem_univ _)) hg hint
  rw [hmean] at key
  exact key
