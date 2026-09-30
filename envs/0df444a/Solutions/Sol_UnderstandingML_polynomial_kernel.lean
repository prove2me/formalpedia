-- Prove2me | solution 1 for UnderstandingML.polynomial_kernel
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-25T18:57:43.276989+00:00
-- url     : https://prove2.me/submissions/7df6e4c1-e80e-41d4-878d-d61e1bfb4881

import Definitions.Def_UnderstandingML_Kernel

open MeasureTheory
open scoped InnerProductSpace

open UnderstandingML

theorem solution (n k : ℕ) :
    ∃ ψ : Vec n → EuclideanSpace ℝ (Fin k → Fin (n + 1)),
      ∀ x x' : Vec n, polynomialKernel k x x' = ⟪ψ x, ψ x'⟫_ℝ := by
  -- the extended vector `(1, x₁, …, xₙ)`, i.e. `x₀ = 1`
  let ext : Vec n → Fin (n + 1) → ℝ := fun x => Fin.cons 1 (fun j => x j)
  refine ⟨fun x => WithLp.toLp 2 (fun J : Fin k → Fin (n + 1) => ∏ i, ext x (J i)),
    fun x x' => ?_⟩
  have h1 : 1 + ⟪x, x'⟫_ℝ = ∑ j, ext x j * ext x' j := by
    rw [Fin.sum_univ_succ]
    simp [ext, PiLp.inner_apply, mul_comm]
  unfold polynomialKernel
  rw [h1, EuclideanSpace.inner_toLp_toLp, ← Fin.prod_const, Fintype.prod_sum]
  simp only [dotProduct, Pi.star_apply, star_trivial, Finset.prod_mul_distrib]
  exact Finset.sum_congr rfl fun J _ => mul_comm _ _
