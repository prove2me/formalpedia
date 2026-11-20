-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalSpecialFibreToPrimeField_proper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:09:31.077226+00:00
-- url     : https://prove2.me/submissions/9ca5c737-7c17-4f6a-9f3c-517c8f49b975

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSecondIntegerHecke
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSpecialFibreFrobenius
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSpecialHecke
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalGluedToSpecZ_proper


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open QEC.Coding.AlgebraicGeometry.SchemeFrobenius
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (l N : ℕ) [Fact l.Prime] [NeZero N] (hN : 0 < N) :
    IsProper (lpsOriginalSpecialFibreToPrimeField l N hN) :=
  IsProper.isStableUnderBaseChange.of_isPullback
    (IsPullback.of_hasPullback (lpsOriginalIntegerNormalGluedToSpecZ N hN)
      (lpsOriginalPrimeSpecToInteger l)) (lpsOriginalIntegerNormalGluedToSpecZ_proper N hN)
end QEC.Coding.TannerLiftedProduct
