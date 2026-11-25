-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.normSq_sum_le_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:25:31.422785+00:00
-- url     : https://prove2.me/submissions/b9468f07-92d7-45c8-bded-c90fe47e4217

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_EventuallyDifferentiableAtOfContDiffAt
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_OfRealNormSqSumMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ComplexConjugate Filter Topology
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
variable {n : ℕ}
namespace ReciprocityTheory.L2DbarEstimates
theorem _root_.solution {m : ℕ} (a : Fin m → ℂ) (u L : Fin m → ℝ) (hu : ∀ i, 0 ≤ u i)
    (hL : ∀ i, 0 ≤ L i) (h : ∀ i, Complex.normSq (a i) ≤ u i * L i) :
    Complex.normSq (∑ i, a i) ≤ (∑ i, u i) * ∑ i, L i := by
  have h1 : ‖∑ i, a i‖ ≤ ∑ i, √(u i) * √(L i) := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [← Real.sqrt_mul (hu i), ← Real.sqrt_sq (norm_nonneg (a i))]
    exact Real.sqrt_le_sqrt (by rw [← normSq_eq_norm_sq]; exact h i)
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => √(u i)) (fun i => √(L i))
  have e1 : ∀ i, √(u i) ^ 2 = u i := fun i => Real.sq_sqrt (hu i)
  have e2 : ∀ i, √(L i) ^ 2 = L i := fun i => Real.sq_sqrt (hL i)
  simp only [e1, e2] at h2
  rw [normSq_eq_norm_sq]
  calc ‖∑ i, a i‖ ^ 2 ≤ (∑ i, √(u i) * √(L i)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := h2
end ReciprocityTheory.L2DbarEstimates
