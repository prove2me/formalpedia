-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.LaurentFiniteWindow.direct_mul_inverse_support_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:31:10.079429+00:00
-- url     : https://prove2.me/submissions/04eb4c3d-970e-4592-ab09-032d16456405

import Mathlib
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_LaurentFiniteWindow
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_LaurentFiniteWindow_direct_support_subset_interval
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_LaurentFiniteWindow_inverse_support_subset_interval

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.LaurentFiniteWindow
open scoped Polynomial Pointwise
variable (k : Type*) [Field k]
namespace QEC.Coding.AlgebraicGeometry.LaurentFiniteWindow
theorem _root_.solution (p q : k[X]) :
    (directCoordinate k p * inverseCoordinate k q).coeff.support ⊆
      Finset.Icc (-(q.natDegree : ℤ)) (p.natDegree : ℤ) := by
  intro n hn
  obtain ⟨i, hi, j, hj, hij⟩ :
      ∃ i ∈ (directCoordinate k p).coeff.support, ∃ j ∈ (inverseCoordinate k q).coeff.support, i + j = n :=
    Finset.mem_add.mp <| AddMonoidAlgebra.support_coeff_mul_subset _ _ hn
  have hibounds := direct_support_subset_interval k p hi
  have hjbounds := inverse_support_subset_interval k q hj
  rw [Finset.mem_Icc] at hibounds hjbounds ⊢
  omega
end QEC.Coding.AlgebraicGeometry.LaurentFiniteWindow
