-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalDelta_j_power
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:38:17.712992+00:00
-- url     : https://prove2.me/submissions/1857f54c-4621-4bb1-b961-0f3ee2f72988

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
theorem _root_.solution (m : ℕ) (τ : ℍ) :
    ModularForm.discriminant τ^m*lpsOriginalJInvariant τ^m=(ModularForm.E₄ τ^3)^m := by
  rw [←mul_pow]
  congr 1
  rw [lpsOriginalJInvariant,mul_div_cancel₀ _ (ModularForm.discriminant_ne_zero τ)]
end QEC.Coding.TannerLiftedProduct
