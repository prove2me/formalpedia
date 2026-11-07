-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalSpecialFibreToPrimeField_locallyOfFinitePresentation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:22:15.032521+00:00
-- url     : https://prove2.me/submissions/aeb5c4f7-5dd5-4b57-96e5-8d4e4596f9e7

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerFlatModel
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSpecialFibreFrobenius
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSpecialFibreFlat
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalGluedToSpecZ_locallyOfFinitePresentation


set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (p : ℕ) [Fact p.Prime] (N : ℕ) [NeZero N] (hN : 0 < N) :
    LocallyOfFinitePresentation (lpsOriginalSpecialFibreToPrimeField p N hN) := by
  exact locallyOfFinitePresentation_isStableUnderBaseChange.of_isPullback
    (CategoryTheory.IsPullback.of_hasPullback
      (lpsOriginalIntegerNormalGluedToSpecZ N hN) (lpsOriginalPrimeSpecToInteger p))
    (lpsOriginalIntegerNormalGluedToSpecZ_locallyOfFinitePresentation N hN)
end QEC.Coding.TannerLiftedProduct
