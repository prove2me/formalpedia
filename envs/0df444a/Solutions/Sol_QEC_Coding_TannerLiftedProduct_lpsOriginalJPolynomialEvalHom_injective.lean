-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalJPolynomialEvalHom_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:43:46.57078+00:00
-- url     : https://prove2.me/submissions/45c1c515-c92a-4574-9b62-4069a3425591

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDilatedModularFunction
import Mathlib.NumberTheory.ModularForms.NormTrace
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Topology.Separation.Connected
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJPolynomial
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJInvariant_range_infinite

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex UpperHalfPlane ModularForm ModularFormClass SlashInvariantFormClass MatrixGroups
open scoped ModularForm UpperHalfPlane
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution :
    Function.Injective lpsOriginalJPolynomialEvalHom := by
  intro P Q h
  apply Polynomial.eq_of_infinite_eval_eq
  apply lpsOriginalJInvariant_range_infinite.mono
  rintro z ⟨τ,rfl⟩
  exact congr_fun h τ
end QEC.Coding.TannerLiftedProduct
