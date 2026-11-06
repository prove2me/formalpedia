-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.LaurentFiniteWindow.direct_mul_inverse_mem_laurentWindow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:30:08.311184+00:00
-- url     : https://prove2.me/submissions/e0c5ed17-3164-4460-901d-e65ded7119d8

import Mathlib
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_LaurentFiniteWindow
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_LaurentFiniteWindow_direct_mul_inverse_support_subset

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.LaurentFiniteWindow
open scoped Polynomial Pointwise
variable (k : Type*) [Field k]
namespace QEC.Coding.AlgebraicGeometry.LaurentFiniteWindow
theorem _root_.solution (p q : k[X]) :
    directCoordinate k p * inverseCoordinate k q ∈
      laurentWindow k (-(q.natDegree : ℤ)) (p.natDegree : ℤ) := by
  change (directCoordinate k p * inverseCoordinate k q).coeff.support ⊆
    Finset.Icc (-(q.natDegree : ℤ)) (p.natDegree : ℤ)
  exact direct_mul_inverse_support_subset k p q
end QEC.Coding.AlgebraicGeometry.LaurentFiniteWindow
