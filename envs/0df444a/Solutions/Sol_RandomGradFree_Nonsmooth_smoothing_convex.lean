-- Prove2me | solution 1 for RandomGradFree.Nonsmooth.smoothing_convex
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:20:15.477852+00:00
-- url     : https://prove2.me/submissions/83aeb43f-cddf-4245-a6f2-3725024d1fc2

import Mathlib
import Definitions.Def_RandomGradFree_Shared_smoothing

open MeasureTheory ProbabilityTheory

namespace RandomGradFree.Nonsmooth

end RandomGradFree.Nonsmooth

open RandomGradFree.Nonsmooth
open MeasureTheory ProbabilityTheory

theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f : E → ℝ) (hf : ConvexOn ℝ Set.univ f)
    (μ : ℝ) (hμ : 0 ≤ μ)
    (hint : ∀ x, Integrable (fun u => f (x + μ • u)) (stdGaussian E)) :
    ConvexOn ℝ Set.univ (RandomGradFree.Shared.smoothing f μ) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  unfold RandomGradFree.Shared.smoothing
  have key : ∀ u : E, f (a • x + b • y + μ • u) ≤ a * f (x + μ • u) + b * f (y + μ • u) := by
    intro u
    have h := hf.2 (Set.mem_univ (x + μ • u)) (Set.mem_univ (y + μ • u)) ha hb hab
    have e : a • (x + μ • u) + b • (y + μ • u) = a • x + b • y + μ • u := by
      rw [smul_add, smul_add, smul_smul, smul_smul, mul_comm a μ, mul_comm b μ, ← smul_smul,
        ← smul_smul]
      calc a • x + μ • a • u + (b • y + μ • b • u)
          = a • x + b • y + μ • (a • u + b • u) := by rw [smul_add]; abel
        _ = a • x + b • y + μ • u := by rw [← add_smul, hab, one_smul]
    rw [e] at h
    simpa [smul_eq_mul] using h
  calc ∫ u, f (a • x + b • y + μ • u) ∂(stdGaussian E)
      ≤ ∫ u, (a * f (x + μ • u) + b * f (y + μ • u)) ∂(stdGaussian E) :=
        integral_mono (hint _) (((hint x).const_mul a).add ((hint y).const_mul b)) key
    _ = a • ∫ u, f (x + μ • u) ∂(stdGaussian E) + b • ∫ u, f (y + μ • u) ∂(stdGaussian E) := by
        rw [integral_add ((hint x).const_mul a) ((hint y).const_mul b), integral_const_mul,
          integral_const_mul, smul_eq_mul, smul_eq_mul]
