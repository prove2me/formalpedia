-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussNormalization_firstFinite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T11:40:46.234393+00:00
-- url     : https://prove2.me/submissions/fa247de2-9e21-491c-bcf3-9c27c6e25ddd

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussFricke
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussSecondResidueDegrees
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussFricke

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N) :
    letI := lpsOriginalRelativeGaussNormalizationCoefficients_algebra N p hNp h4N hN hpN
    Module.Finite (LPSOriginalGaussAffineOrder N hN p)
      (LPSOriginalRelativeGaussNormalization N p hNp h4N hN) := by
  let := lpsOriginalRelativeGaussNormalizationCoefficients_algebra N p hNp h4N hN hpN
  let : Module.Finite (LPSOriginalGaussAffineOrder N hN p)
      (LPSOriginalRelativeGaussHeckeOrder N hN p) :=
    (lpsOriginalRelativeGaussHeckePolynomial_monic N hN p).finite_adjoinRoot
  exact Module.Finite.equiv
    (lpsOriginalRelativeGaussNormalizationAffineEquiv N p hNp h4N hN hpN).toLinearEquiv
end QEC.Coding.TannerLiftedProduct
