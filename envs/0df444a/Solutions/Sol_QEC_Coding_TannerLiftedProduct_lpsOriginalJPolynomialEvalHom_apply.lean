-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalJPolynomialEvalHom_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:35:20.290695+00:00
-- url     : https://prove2.me/submissions/bc20930d-74c1-47f1-a4e4-5440476b7187

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDilatedModularFunction
import Mathlib.NumberTheory.ModularForms.NormTrace
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Topology.Separation.Connected
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJPolynomial

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex UpperHalfPlane ModularForm ModularFormClass SlashInvariantFormClass MatrixGroups
open scoped ModularForm UpperHalfPlane
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (P : Polynomial ℂ) (τ : ℍ) :
    lpsOriginalJPolynomialEvalHom P τ=P.eval (lpsOriginalJInvariant τ) := rfl
end QEC.Coding.TannerLiftedProduct
