-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalJ_jN_algebraic_relation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:08:47.877034+00:00
-- url     : https://prove2.me/submissions/0b9700a0-4287-4c02-ba1d-de09547e91ac

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJPolynomial
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.LinearAlgebra.Lagrange
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularEquation
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalModularEquationComplex_original_root
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalModularEquationComplex_nonzero

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex UpperHalfPlane ModularForm ModularFormClass SlashInvariantFormClass MatrixGroups
open scoped ModularForm UpperHalfPlane
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N] (hN : 0<N) :
    ∃ Φ : Polynomial (Polynomial ℂ), Φ≠0 ∧ ∀ τ : ℍ,
      Φ.eval₂ (Polynomial.evalRingHom (lpsOriginalJInvariant τ))
        (lpsOriginalJDilated N hN τ)=0 :=
  ⟨lpsOriginalModularEquationComplex N hN,
    lpsOriginalModularEquationComplex_nonzero N hN,
    lpsOriginalModularEquationComplex_original_root N hN⟩
end QEC.Coding.TannerLiftedProduct
