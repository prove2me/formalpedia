-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsIntegralCuspCoordinates_cast
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:35:41.463665+00:00
-- url     : https://prove2.me/submissions/2691dc43-5c67-49d3-b06e-16aad5eaf7a1

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCongruenceFiniteDimension
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCoefficients
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaEisensteinCorrection
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.LinearMap
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspIntegralHecke

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Polynomial
open scoped MatrixGroups UpperHalfPlane ModularForm
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) (f : lpsIntegralCuspLattice N)
    (i : Fin (lpsGamma0CoefficientCount N 2)) :
    (lpsIntegralCuspCoordinates N f i : ℂ) = lpsCuspCoefficient N i.val f :=
  (f.property i.val).choose_spec.symm
end QEC.Coding.TannerLiftedProduct
