-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalE4DilatedForm_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:10:40.872187+00:00
-- url     : https://prove2.me/submissions/281d83e3-9dfe-4bc9-95b7-2f2c7438bb21

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJPolynomial
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.LinearAlgebra.Lagrange
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularEquation

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex UpperHalfPlane ModularForm ModularFormClass SlashInvariantFormClass MatrixGroups
open scoped ModularForm UpperHalfPlane
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) (hN : 0<N) (τ : ℍ) :
    lpsOriginalE4DilatedForm N hN τ=
      ((ModularForm.E₄:ℍ→ℂ) ∣[(4:ℤ)] lpsE2AffineMatrix N hN 0) τ := rfl
end QEC.Coding.TannerLiftedProduct
