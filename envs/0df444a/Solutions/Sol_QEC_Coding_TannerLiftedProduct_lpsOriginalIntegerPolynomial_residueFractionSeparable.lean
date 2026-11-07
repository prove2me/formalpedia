-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerPolynomial_residueFractionSeparable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:01:59.488203+00:00
-- url     : https://prove2.me/submissions/69f59bd4-1b6e-4a36-ab66-a30cf003e84e

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerAffineModel
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCosetCuspSeries
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalAnalyticCuspLocalization
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCoprimeModularReduction
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerPolynomial_residueCosetProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCosetResidueCuspSeries_injective
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2TwistModularForm_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_one
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero_even
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero_odd
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_one
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsQuadraticE2TwistModularForm_apply
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open Filter Topology
open scoped UpperHalfPlane MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
attribute [local instance] lpsOriginalLevelPhasePrime_isMaximal
attribute [local instance] lpsOriginalLevelPhaseResidue_field
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalFieldCuspSeries_domain
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) (hp : p.Prime) (hpN : ¬ p ∣ N) :
    ((lpsOriginalIntegerPolynomial N hN).map
      ((algebraMap (lpsOriginalCuspSeriesRing (LPSOriginalLevelPhaseResidue N hN p hp))
          (FractionRing (lpsOriginalCuspSeriesRing (LPSOriginalLevelPhaseResidue N hN p hp)))).comp
        (lpsOriginalResidueLevelCoefficientEval N hN p hp))).Separable := by
  classical
  let := Fintype.ofFinite (LPSOriginalCuspIndex N)
  rw [← Polynomial.map_map,lpsOriginalIntegerPolynomial_residueCosetProduct,
    Polynomial.map_prod]
  simp only [Polynomial.map_sub,Polynomial.map_X,Polynomial.map_C]
  apply Polynomial.separable_prod_X_sub_C_iff.mpr
  exact (IsFractionRing.injective
    (lpsOriginalCuspSeriesRing (LPSOriginalLevelPhaseResidue N hN p hp))
    (FractionRing (lpsOriginalCuspSeriesRing (LPSOriginalLevelPhaseResidue N hN p hp)))).comp
    (lpsOriginalCosetResidueCuspSeries_injective N hN p hp hpN)
end QEC.Coding.TannerLiftedProduct
