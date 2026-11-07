-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsIntegralCuspLattice_finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:39:00.001195+00:00
-- url     : https://prove2.me/submissions/79ac3cef-2c81-44e6-9054-ecce336d256a

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCongruenceFiniteDimension
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCoefficients
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaEisensteinCorrection
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.LinearMap
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspIntegralHecke
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsIntegralCuspCoordinates_injective

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Polynomial
open scoped MatrixGroups UpperHalfPlane ModularForm
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N] :
    Module.Finite ℤ (lpsIntegralCuspLattice N) :=
  Module.Finite.of_injective (lpsIntegralCuspCoordinates N) (lpsIntegralCuspCoordinates_injective N)
end QEC.Coding.TannerLiftedProduct
