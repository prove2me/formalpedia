-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussNormalizationCoefficients_isIntegral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T11:00:17.097007+00:00
-- url     : https://prove2.me/submissions/2375c921-2e24-4c10-bb73-2435496ba8c4

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussFrobeniusDescent
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussSecondUnits

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N) :
    (lpsOriginalRelativeGaussNormalizationCoefficients N p hNp h4N hN hpN).IsIntegral := by
  let R := LPSOriginalGaussAffineOrder N hN p
  let B := LPSOriginalRelativeGaussHeckeOrder N hN p
  let C := LPSOriginalRelativeGaussNormalization N p hNp h4N hN
  let : Module.Finite R B := (lpsOriginalRelativeGaussHeckePolynomial_monic N hN p).finite_adjoinRoot
  let := lpsOriginalRelativeGaussNormalizationCoefficients_algebra N p hNp h4N hN hpN
  let e := lpsOriginalRelativeGaussNormalizationAffineEquiv N p hNp h4N hN hpN
  let : Algebra.IsIntegral R C := e.isIntegral_iff.mp inferInstance
  exact Algebra.IsIntegral.isIntegral
end QEC.Coding.TannerLiftedProduct
