-- Prove2me | solution 1 for circle_center_mem_of_isCompact_nonempty_convex_of_global_polynomial_bound_of_forall_symmetrized_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:31:47.177902+00:00
-- url     : https://prove2.me/submissions/fe509df2-3c5d-4f39-9055-3a4f49c179d7

import Definitions.Def_Operator_Crouzeix_ConvexRunge
import Definitions.Def_Operator_Crouzeix_NormalProduct
import Definitions.Def_Operator_Crouzeix_SmoothSupportDomain
import Definitions.Def_Operator_NumericalRange_Convex
import Definitions.Def_Operator_NumericalRange_Nonempty
import Definitions.Def_Operator_Crouzeix_NormalProductSymmetrized
import Theorems.Thm_circle_center_mem_of_isCompact_nonempty_convex_of_forall_symmetrized_bound

set_option autoImplicit false
open Complex Polynomial Set
open scoped InnerProductSpace Pointwise
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution
    [Nontrivial E] (A : E →L[ℂ] E) {K : Set ℂ}
    (hcompact : IsCompact K) (hnonempty : K.Nonempty) (hconvex : Convex ℝ K)
    (c : ℂ) {R : ℝ}
    (hA : ‖A - c • (1 : E →L[ℂ] E)‖ < R)
    (C : ℝ) (_hC : 0 ≤ C)
    (_hcalc : ∀ q : Polynomial ℂ,
      ‖Polynomial.aeval A q‖ ≤ C * polynomialSupNorm q K)
    (hsymm : ∀ q : Polynomial ℂ,
      ‖Polynomial.aeval A q +
          star (crouzeixPolynomialAuxiliaryOperator A
            (SmoothJordanDomain.ball c R
              ((norm_nonneg (A - c • 1)).trans_lt hA)) q)‖ ≤
        2 * polynomialSupNorm q K) :
    c ∈ K := by
  exact
    circle_center_mem_of_isCompact_nonempty_convex_of_forall_symmetrized_bound
      A hcompact hnonempty hconvex c hA hsymm
