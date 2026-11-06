-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.LaurentFiniteWindow.laurentWindow_eq_span
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:31:14.811743+00:00
-- url     : https://prove2.me/submissions/1f03cdff-5868-4846-b6a2-170a8fcab620

import Mathlib
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_LaurentFiniteWindow
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_LaurentFiniteWindow_T_mem_laurentWindow
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_LaurentFiniteWindow_laurent_sum_C_mul_T_eq

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.LaurentFiniteWindow
open scoped Polynomial Pointwise
variable (k : Type*) [Field k]
namespace QEC.Coding.AlgebraicGeometry.LaurentFiniteWindow
theorem _root_.solution (lower upper : ℤ) :
    laurentWindow k lower upper =
      Submodule.span k (laurentWindowFamily k lower upper : Set (LaurentPolynomial k)) := by
  classical
  apply le_antisymm
  · intro f hf
    change f.coeff.support ⊆ Finset.Icc lower upper at hf
    rw [← laurent_sum_C_mul_T_eq k f]
    exact Submodule.sum_mem _ fun n hn => by
      rw [← LaurentPolynomial.smul_eq_C_mul]
      exact Submodule.smul_mem _ _ <| Submodule.subset_span <|
        Finset.mem_image.mpr ⟨n, hf hn, rfl⟩
  · refine Submodule.span_le.mpr ?_
    intro f hf
    change f ∈ laurentWindowFamily k lower upper at hf
    rcases Finset.mem_image.mp hf with ⟨n, hn, rfl⟩
    exact T_mem_laurentWindow k hn
end QEC.Coding.AlgebraicGeometry.LaurentFiniteWindow
