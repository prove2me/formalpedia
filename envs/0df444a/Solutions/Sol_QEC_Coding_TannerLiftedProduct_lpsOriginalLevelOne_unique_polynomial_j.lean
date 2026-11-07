-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalLevelOne_unique_polynomial_j
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:46:06.840837+00:00
-- url     : https://prove2.me/submissions/0874fe03-dacf-4a10-bbd8-2610e2068ab5

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDilatedModularFunction
import Mathlib.NumberTheory.ModularForms.NormTrace
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Topology.Separation.Connected
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJPolynomial
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalLevelOne_polynomial_j
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJPolynomialEvalHom_injective

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex UpperHalfPlane ModularForm ModularFormClass SlashInvariantFormClass MatrixGroups
open scoped ModularForm UpperHalfPlane
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (m : ℕ)
    (f : ModularForm 𝒮ℒ (12*(m:ℤ))) :
    ∃! P : Polynomial ℂ, P.natDegree≤m ∧ ∀ τ : ℍ,
      f τ=ModularForm.discriminant τ^m*P.eval (lpsOriginalJInvariant τ) := by
  obtain ⟨P,hP,hPeval⟩ := lpsOriginalLevelOne_polynomial_j m f
  refine ⟨P,⟨hP,hPeval⟩,?_⟩
  intro Q hQ
  apply lpsOriginalJPolynomialEvalHom_injective
  funext τ
  apply mul_left_cancel₀ (pow_ne_zero m (ModularForm.discriminant_ne_zero τ))
  exact (hQ.2 τ).symm.trans (hPeval τ)
end QEC.Coding.TannerLiftedProduct
