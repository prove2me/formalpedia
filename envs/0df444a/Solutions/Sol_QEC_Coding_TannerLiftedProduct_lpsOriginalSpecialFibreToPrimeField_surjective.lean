-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalSpecialFibreToPrimeField_surjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:15:05.071686+00:00
-- url     : https://prove2.me/submissions/09d81626-8cde-4747-8403-adf4f1261ad3

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerFlatModel
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSpecialFibreFrobenius
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSpecialFibreFlat
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalGluedToSpecZ_surjective


set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (p : ℕ) [Fact p.Prime] (N : ℕ) (hN : 0 < N) :
    Surjective (lpsOriginalSpecialFibreToPrimeField p N hN) := by
  exact (inferInstance : MorphismProperty.IsStableUnderBaseChange (@Surjective.{0})).of_isPullback
    (CategoryTheory.IsPullback.of_hasPullback
      (lpsOriginalIntegerNormalGluedToSpecZ N hN) (lpsOriginalPrimeSpecToInteger p))
    (lpsOriginalIntegerNormalGluedToSpecZ_surjective N hN)
end QEC.Coding.TannerLiftedProduct
