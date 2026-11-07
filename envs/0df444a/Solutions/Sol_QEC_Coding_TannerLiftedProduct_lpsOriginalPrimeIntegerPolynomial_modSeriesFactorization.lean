-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalPrimeIntegerPolynomial_modSeriesFactorization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:38:36.539566+00:00
-- url     : https://prove2.me/submissions/784fef18-4da1-441f-8f3f-0a2b2d98fd45

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeModularBranches
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalAnalyticCuspLocalization
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeCuspCorrespondence
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalPrimeIntegerPolynomial_cyclotomicFormalProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalModPrimeCoefficientEval_reduction
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCyclotomicFormalPrimeProduct_reduction


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (p : ℕ) [Fact p.Prime] :
    (lpsOriginalIntegerPolynomial p (Fact.out : p.Prime).pos).map
      (lpsOriginalModPrimeCoefficientEval p)=
      (Polynomial.X-Polynomial.C
          ((lpsOriginalCuspJWidth (ZMod p) p (Fact.out : p.Prime).ne_zero)^p)) *
        (Polynomial.X^p-Polynomial.C
          (lpsOriginalCuspJWidth (ZMod p) p (Fact.out : p.Prime).ne_zero)) := by
  have h:=congrArg (Polynomial.map (lpsOriginalCyclotomicCuspReduction p))
    (lpsOriginalPrimeIntegerPolynomial_cyclotomicFormalProduct p)
  rw [Polynomial.map_map,lpsOriginalModPrimeCoefficientEval_reduction,
    lpsOriginalCyclotomicFormalPrimeProduct_reduction] at h
  exact h
end QEC.Coding.TannerLiftedProduct
