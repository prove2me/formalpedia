-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerFrickeOriginalDenominator_coeff_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T08:53:54.507854+00:00
-- url     : https://prove2.me/submissions/6c897028-25da-40b5-a6f6-316f85930108

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerLevelFunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalZeroNormalizationComparison
import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.Algebra.Polynomial.Reverse
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegralFricke

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane MatrixGroups
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    (lpsOriginalIntegerFrickeReciprocalDenominator
      (lpsOriginalIntegerPolynomial N hN)).coeff 0 = 1 :=
  lpsOriginalIntegerFrickeReciprocalDenominator_coeff_zero _
    (lpsOriginalIntegerPolynomial_monic N hN)
end QEC.Coding.TannerLiftedProduct
