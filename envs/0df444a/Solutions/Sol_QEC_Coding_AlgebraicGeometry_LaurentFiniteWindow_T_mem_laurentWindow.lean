-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.LaurentFiniteWindow.T_mem_laurentWindow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:29:14.445398+00:00
-- url     : https://prove2.me/submissions/b23b8dfd-1c30-42c9-9958-2f302a7d792d

import Mathlib
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_LaurentFiniteWindow

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.LaurentFiniteWindow
open scoped Polynomial Pointwise
variable (k : Type*) [Field k]
namespace QEC.Coding.AlgebraicGeometry.LaurentFiniteWindow
theorem _root_.solution {lower upper n : ℤ} (hn : n ∈ Finset.Icc lower upper) :
    LaurentPolynomial.T (R := k) n ∈ laurentWindow k lower upper := by
  have hsupport : (LaurentPolynomial.T (R := k) n).coeff.support ⊆ ({n} : Finset ℤ) := by
    exact Finsupp.support_single_subset
  exact hsupport.trans <| by
    intro m hm
    have hmn : m = n := Finset.mem_singleton.mp hm
    simpa [hmn] using hn
end QEC.Coding.AlgebraicGeometry.LaurentFiniteWindow
