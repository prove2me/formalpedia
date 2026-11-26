-- Prove2me | solution 1 for circle_center_mem_closure_numericalRange_of_global_polynomial_bound_of_forall_symmetrized_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:31:58.328514+00:00
-- url     : https://prove2.me/submissions/f75e1181-7e1c-4531-b230-cf7bf5d3d8e7

import Definitions.Def_Operator_Crouzeix_ConvexRunge
import Definitions.Def_Operator_Crouzeix_NormalProduct
import Definitions.Def_Operator_Crouzeix_SmoothSupportDomain
import Definitions.Def_Operator_NumericalRange_Convex
import Definitions.Def_Operator_NumericalRange_Nonempty
import Definitions.Def_Operator_Crouzeix_NormalProductSymmetrized
import Theorems.Thm_circle_center_mem_of_isCompact_nonempty_convex_of_forall_symmetrized_bound
import Theorems.Thm_closure_numericalRange_nonempty_iff_nontrivial
import Theorems.Thm_convex_numericalRange
import Theorems.Thm_isBounded_numericalRange


set_option autoImplicit false
open Complex Polynomial Set
open scoped InnerProductSpace Pointwise
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution
    [Nontrivial E] (A : E →L[ℂ] E) (c : ℂ) {R : ℝ}
    (hA : ‖A - c • (1 : E →L[ℂ] E)‖ < R)
    (C : ℝ) (_hC : 0 ≤ C)
    (_hcalc : ∀ q : Polynomial ℂ,
      ‖Polynomial.aeval A q‖ ≤
        C * polynomialSupNorm q (closure (numericalRange A)))
    (hsymm : ∀ q : Polynomial ℂ,
      ‖Polynomial.aeval A q +
          star (crouzeixPolynomialAuxiliaryOperator A
            (SmoothJordanDomain.ball c R
              ((norm_nonneg (A - c • 1)).trans_lt hA)) q)‖ ≤
        2 * polynomialSupNorm q (closure (numericalRange A))) :
    c ∈ closure (numericalRange A) := by
  exact
    circle_center_mem_of_isCompact_nonempty_convex_of_forall_symmetrized_bound
      A (isBounded_numericalRange A).isCompact_closure
        ((closure_numericalRange_nonempty_iff_nontrivial A).2 inferInstance)
        (convex_numericalRange A).closure c hA hsymm
