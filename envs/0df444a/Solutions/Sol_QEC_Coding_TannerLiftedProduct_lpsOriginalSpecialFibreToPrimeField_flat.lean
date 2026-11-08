-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalSpecialFibreToPrimeField_flat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:28:06.95873+00:00
-- url     : https://prove2.me/submissions/3ba5c942-7ad3-418b-af32-09894524ec44

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerFlatModel
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSpecialFibreFrobenius
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSpecialFibreFlat
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalGluedToSpecZ_flat


set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (p : ℕ) [Fact p.Prime] (N : ℕ) (hN : 0 < N) :
    Flat (lpsOriginalSpecialFibreToPrimeField p N hN) := by
  exact Flat.isStableUnderBaseChange.of_isPullback
    (CategoryTheory.IsPullback.of_hasPullback
      (lpsOriginalIntegerNormalGluedToSpecZ N hN) (lpsOriginalPrimeSpecToInteger p))
    (lpsOriginalIntegerNormalGluedToSpecZ_flat N hN)
end QEC.Coding.TannerLiftedProduct
