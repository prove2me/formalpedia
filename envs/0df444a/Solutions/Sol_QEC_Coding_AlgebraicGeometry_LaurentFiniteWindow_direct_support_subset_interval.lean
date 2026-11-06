-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.LaurentFiniteWindow.direct_support_subset_interval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:05:14.775332+00:00
-- url     : https://prove2.me/submissions/ca7d7b16-6fee-430a-b6b4-58b844a5db19

import Mathlib
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_LaurentFiniteWindow
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_LaurentFiniteWindow_directCoordinate_apply

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.LaurentFiniteWindow
open scoped Polynomial Pointwise
variable (k : Type*) [Field k]
namespace QEC.Coding.AlgebraicGeometry.LaurentFiniteWindow
theorem _root_.solution (p : k[X]) :
    (directCoordinate k p).coeff.support ⊆ Finset.Icc (0 : ℤ) (p.natDegree : ℤ) := by
  rw [directCoordinate_apply, LaurentPolynomial.support_coeff_toLaurent]
  rintro n hn
  rcases Finset.mem_map.mp hn with ⟨m, hm, rfl⟩
  refine Finset.mem_Icc.mpr ⟨Int.natCast_nonneg _, ?_⟩
  exact Int.ofNat_le.mpr (Polynomial.le_natDegree_of_mem_supp m hm)
end QEC.Coding.AlgebraicGeometry.LaurentFiniteWindow
