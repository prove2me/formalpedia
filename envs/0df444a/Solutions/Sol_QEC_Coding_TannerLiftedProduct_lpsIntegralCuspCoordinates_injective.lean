-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsIntegralCuspCoordinates_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:37:34.686119+00:00
-- url     : https://prove2.me/submissions/0901f49c-a91b-4bdc-bcdb-2bb2b895100a

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCongruenceFiniteDimension
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCoefficients
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaEisensteinCorrection
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.LinearMap
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspIntegralHecke
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsIntegralCuspCoordinates_cast

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Polynomial
open scoped MatrixGroups UpperHalfPlane ModularForm
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N] :
    Function.Injective (lpsIntegralCuspCoordinates N) := by
  intro f g h
  apply Subtype.ext
  apply CuspForm.toModularFormₗ_injective
  apply lpsGamma0FiniteCoefficients_injective N 2
  ext i
  change lpsCuspCoefficient N i.val f = lpsCuspCoefficient N i.val g
  rw [← lpsIntegralCuspCoordinates_cast N f i, ← lpsIntegralCuspCoordinates_cast N g i]
  exact congrArg (fun v => (v i : ℂ)) h
end QEC.Coding.TannerLiftedProduct
