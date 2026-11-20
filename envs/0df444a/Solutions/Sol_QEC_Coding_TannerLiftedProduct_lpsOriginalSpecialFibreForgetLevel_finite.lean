-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalSpecialFibreForgetLevel_finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:16:54.178849+00:00
-- url     : https://prove2.me/submissions/3dbd63f1-3fe6-4ceb-8c59-4ca58652d0aa

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSecondIntegerHecke
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSpecialFibreFrobenius
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSpecialHecke
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalSpecialFibreLift_finite
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalGluedForgetLevel_finite


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open QEC.Coding.AlgebraicGeometry.SchemeFrobenius
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (l N M : ℕ) [Fact l.Prime] [NeZero N] [NeZero M]
    (hNM : N ∣ M) (h4N : 4 ∣ N) (hN : 0 < N) (hM : 0 < M) :
    IsFinite (lpsOriginalSpecialFibreForgetLevel l N M hNM h4N hN hM) :=
  lpsOriginalSpecialFibreLift_finite _ _ _ _ _ _ _
    (lpsOriginalIntegerNormalGluedForgetLevel_finite N M hNM h4N hN hM)
end QEC.Coding.TannerLiftedProduct
