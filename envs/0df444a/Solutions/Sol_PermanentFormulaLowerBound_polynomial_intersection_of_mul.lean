-- Prove2me | solution 1 for PermanentFormulaLowerBound.polynomial_intersection_of_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:12.090475+00:00
-- url     : https://prove2.me/submissions/76e48f93-b305-4de7-9387-147831c8c50e

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentFormulaLowerBound_polynomialCoefficientProjection_map_mul
import Theorems.Thm_PermanentFormulaLowerBound_polynomialCoefficientProjection_map

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
noncomputable section
variable {K E ι : Type*} [Field K] [Field E] [Algebra K E]
namespace PermanentFormulaLowerBound
theorem _root_.solution
    (f : MvPolynomial ι E) (p q : MvPolynomial ι K)
    (hq : q ≠ 0)
    (h : MvPolynomial.map (algebraMap K E) q * f =
      MvPolynomial.map (algebraMap K E) p) :
    ∃ g : MvPolynomial ι K,
      MvPolynomial.map (algebraMap K E) g = f := by
  classical
  let j : K →ₗ[K] E := Algebra.linearMap K E
  have hj : LinearMap.ker j = ⊥ :=
    LinearMap.ker_eq_bot.mpr (RingHom.injective (algebraMap K E))
  let φ : E →ₗ[K] K := j.leftInverse
  have hφ (a : K) : φ (algebraMap K E a) = a :=
    LinearMap.leftInverse_apply_of_inj hj a
  let g : MvPolynomial ι K := polynomialCoefficientProjection φ f
  have hg : q * g = p := by
    have he := congrArg (polynomialCoefficientProjection φ) h
    simpa [g, polynomialCoefficientProjection_map_mul,
      polynomialCoefficientProjection_map φ hφ] using he
  refine ⟨g, ?_⟩
  have hq' : MvPolynomial.map (algebraMap K E) q ≠ 0 := by
    intro hzero
    apply hq
    apply MvPolynomial.map_injective (algebraMap K E)
      (RingHom.injective (algebraMap K E))
    simpa using hzero
  apply mul_left_cancel₀ hq'
  calc
    MvPolynomial.map (algebraMap K E) q *
        MvPolynomial.map (algebraMap K E) g =
      MvPolynomial.map (algebraMap K E) (q * g) := by rw [map_mul]
    _ = MvPolynomial.map (algebraMap K E) p := congrArg _ hg
    _ = MvPolynomial.map (algebraMap K E) q * f := h.symm
end PermanentFormulaLowerBound
