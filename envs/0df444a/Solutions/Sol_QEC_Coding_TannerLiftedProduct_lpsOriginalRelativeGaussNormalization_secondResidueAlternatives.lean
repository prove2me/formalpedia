-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussNormalization_secondResidueAlternatives
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:44:42.708296+00:00
-- url     : https://prove2.me/submissions/207af11d-d96c-4c56-bab4-78d4b4af2351

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussFirstResidueCoordinate
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussSecondCoordinates
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussSecondBranches
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalPrimeIntegerPolynomial_charPRoot_iff
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussNormalization_secondPrimeRoot


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (A : Type*) [CommRing A] [IsDomain A] [Algebra (ZMod p) A]
    (f : LPSOriginalRelativeGaussNormalization N p hNp h4N hN →+* A) :
    f (lpsOriginalRelativeGaussNormalizationSecondJ N p hNp h4N hN) =
        (f (lpsOriginalRelativeGaussNormalizationFirstJ N p hNp h4N hN hpN))^p ∨
      (f (lpsOriginalRelativeGaussNormalizationSecondJ N p hNp h4N hN))^p =
        f (lpsOriginalRelativeGaussNormalizationFirstJ N p hNp h4N hN hpN) := by
  have h := congrArg f
    (lpsOriginalRelativeGaussNormalization_secondPrimeRoot N p hNp h4N hN hpN)
  rw [Polynomial.hom_eval₂,map_zero,
    lpsOriginalBivariateIntegerCoefficientEval_comp_hom] at h
  exact (lpsOriginalPrimeIntegerPolynomial_charPRoot_iff p A _ _).mp h
end QEC.Coding.TannerLiftedProduct
