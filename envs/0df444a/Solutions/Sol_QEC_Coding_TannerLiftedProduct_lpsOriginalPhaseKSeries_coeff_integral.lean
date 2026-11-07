-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalPhaseKSeries_coeff_integral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:22:00.246554+00:00
-- url     : https://prove2.me/submissions/887c894a-5146-4a52-8ae1-f7dbffcf4cbd

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
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRationalNomePhase_integral

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (r : ℚ) (n : ℕ) :
    IsIntegral ℤ ((PowerSeries.rescale (Function.Periodic.qParam 1 (r : ℂ))
      (PowerSeries.map (algebraMap ℤ ℂ) lpsOriginalJZSeries)).coeff n) := by
  rw [PowerSeries.coeff_rescale, PowerSeries.coeff_map]
  exact ((lpsOriginalRationalNomePhase_integral r).pow n).mul
    (isIntegral_algebraMap (R := ℤ) (A := ℂ))
end QEC.Coding.TannerLiftedProduct
