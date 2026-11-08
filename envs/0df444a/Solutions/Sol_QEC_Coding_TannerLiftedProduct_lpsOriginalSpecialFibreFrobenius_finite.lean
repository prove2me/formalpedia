-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalSpecialFibreFrobenius_finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:21:01.694351+00:00
-- url     : https://prove2.me/submissions/26e9c5fc-5366-45a6-91c7-f9ae27d87966

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_AbsoluteFrobenius
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerProperModel
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSpecialFibreFrobenius
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_SchemeFrobenius_absoluteFrobenius_finite
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalGluedToSpecZ_proper


set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
open QEC.Coding.AlgebraicGeometry.SchemeFrobenius
variable (p : ℕ) [Fact p.Prime] (N : ℕ) (hN : 0<N)
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution [NeZero N] : IsFinite (lpsOriginalSpecialFibreFrobenius p N hN) := by
  let : LocallyOfFiniteType (lpsOriginalSpecialFibreToPrimeField p N hN) := by
    exact _root_.AlgebraicGeometry.locallyOfFiniteType_isStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback (lpsOriginalIntegerNormalGluedToSpecZ N hN)
        (lpsOriginalPrimeSpecToInteger p))
      (lpsOriginalIntegerNormalGluedToSpecZ_proper N hN).toLocallyOfFiniteType
  exact absoluteFrobenius_finite p _ (lpsOriginalSpecialFibreToPrimeField p N hN)
end QEC.Coding.TannerLiftedProduct
