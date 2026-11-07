-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalClearedAffineCusp_integral_coeff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:51:26.477351+00:00
-- url     : https://prove2.me/submissions/73f76b42-b98e-4372-8fde-41df459f70ea

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalExactFunctionFieldDegree
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalExactStabilizer
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerQExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalModularEquation
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.Minpoly
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Polynomial.ScaleRoots
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModularEquation
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalAffineKSeries_coeff_integral
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRationalNomePhase_inv_integral
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalClearedAffineCusp_taylor

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (B m : ℕ) (hm : m≠0) (r : ℚ) (n : ℕ) :
    IsIntegral ℤ ((lpsOriginalTaylorSeries
      (lpsOriginalClearedAffineCusp B m r)).coeff n) := by
  rw [lpsOriginalClearedAffineCusp_taylor B m hm r,
    PowerSeries.coeff_C_mul,PowerSeries.coeff_X_pow_mul']
  split_ifs
  · exact (lpsOriginalRationalNomePhase_inv_integral r).mul
      (lpsOriginalAffineKSeries_coeff_integral r m hm _)
  · rw [mul_zero]
    exact isIntegral_zero
end QEC.Coding.TannerLiftedProduct
