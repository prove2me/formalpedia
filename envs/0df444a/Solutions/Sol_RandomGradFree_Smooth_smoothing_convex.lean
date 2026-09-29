-- Prove2me | solution 1 for RandomGradFree.Smooth.smoothing_convex
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:21:17.843912+00:00
-- url     : https://prove2.me/submissions/7a7aad10-76b9-4533-9c86-132a66860ceb

import Mathlib
import Definitions.Def_RandomGradFree_Shared_smoothing

open MeasureTheory ProbabilityTheory

namespace RandomGradFree.Smooth

end RandomGradFree.Smooth

open RandomGradFree.Smooth

theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f : E → ℝ) (hf : ConvexOn ℝ Set.univ f)
    (μ : ℝ) (hμ : 0 ≤ μ)
    (hint : ∀ x, Integrable (fun u => f (x + μ • u)) (stdGaussian E)) :
    ConvexOn ℝ Set.univ (RandomGradFree.Shared.smoothing f μ) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  unfold RandomGradFree.Shared.smoothing
  have hpt : ∀ u : E, f (a • x + b • y + μ • u) ≤ a * f (x + μ • u) + b * f (y + μ • u) := by
    intro u
    have heq : a • x + b • y + μ • u = a • (x + μ • u) + b • (y + μ • u) := by
      have : μ • u = a • (μ • u) + b • (μ • u) := by rw [← add_smul, hab, one_smul]
      rw [smul_add, smul_add]
      conv_lhs => rw [this]
      abel
    rw [heq]
    exact hf.2 (Set.mem_univ _) (Set.mem_univ _) ha hb hab
  have hi1 := hint (a • x + b • y)
  have hi2 : Integrable (fun u => a * f (x + μ • u) + b * f (y + μ • u)) (stdGaussian E) :=
    ((hint x).const_mul a).add ((hint y).const_mul b)
  calc ∫ u, f (a • x + b • y + μ • u) ∂(stdGaussian E)
      ≤ ∫ u, (a * f (x + μ • u) + b * f (y + μ • u)) ∂(stdGaussian E) :=
        integral_mono hi1 hi2 hpt
    _ = a • ∫ u, f (x + μ • u) ∂(stdGaussian E) + b • ∫ u, f (y + μ • u) ∂(stdGaussian E) := by
        rw [integral_add ((hint x).const_mul a) ((hint y).const_mul b), integral_const_mul,
          integral_const_mul, smul_eq_mul, smul_eq_mul]
