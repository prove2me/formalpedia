-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.LaurentFiniteWindow.opposite_scaled_intersection_mem_laurentWindow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:30:16.343344+00:00
-- url     : https://prove2.me/submissions/8b15d2cd-c275-4ddd-8454-c28062d108fe

import Mathlib
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_LaurentFiniteWindow
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_LaurentFiniteWindow_direct_mul_inverse_support_subset

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.LaurentFiniteWindow
open scoped Polynomial Pointwise
variable (k : Type*) [Field k]
namespace QEC.Coding.AlgebraicGeometry.LaurentFiniteWindow
theorem _root_.solution
    {a b : k[X]} {z : LaurentPolynomial k}
    (hzDirect : z ∈ directScaledLocus k a)
    (hzInverse : z ∈ inverseScaledLocus k b) :
    inverseCoordinate k b * (directCoordinate k a * z) ∈
      laurentWindow k (-(b.natDegree : ℤ)) (a.natDegree : ℤ) := by
  change ∃ p : k[X], directCoordinate k a * z = directCoordinate k p at hzDirect
  change ∃ q : k[X], inverseCoordinate k b * z = inverseCoordinate k q at hzInverse
  rcases hzDirect with ⟨p, hp⟩
  rcases hzInverse with ⟨q, hq⟩
  change (inverseCoordinate k b * (directCoordinate k a * z)).coeff.support ⊆
    Finset.Icc (-(b.natDegree : ℤ)) (a.natDegree : ℤ)
  intro n hn
  have hleft : n ∈ Finset.Icc (-(b.natDegree : ℤ)) (p.natDegree : ℤ) := by
    apply direct_mul_inverse_support_subset k p b
    simpa [hp, mul_comm] using hn
  have hscaled : inverseCoordinate k b * (directCoordinate k a * z) =
      directCoordinate k a * inverseCoordinate k q := by
    calc
      inverseCoordinate k b * (directCoordinate k a * z) =
          (inverseCoordinate k b * directCoordinate k a) * z := (mul_assoc _ _ _).symm
      _ = (directCoordinate k a * inverseCoordinate k b) * z := by
        rw [mul_comm (inverseCoordinate k b) (directCoordinate k a)]
      _ = directCoordinate k a * (inverseCoordinate k b * z) := mul_assoc _ _ _
      _ = directCoordinate k a * inverseCoordinate k q := by rw [hq]
  have hright : n ∈ Finset.Icc (-(q.natDegree : ℤ)) (a.natDegree : ℤ) := by
    apply direct_mul_inverse_support_subset k a q
    simpa [hscaled] using hn
  rw [Finset.mem_Icc] at hleft hright ⊢
  exact ⟨hleft.1, hright.2⟩
end QEC.Coding.AlgebraicGeometry.LaurentFiniteWindow
