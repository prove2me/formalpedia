-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalGluedForgetLevel_surjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:17:52.805461+00:00
-- url     : https://prove2.me/submissions/4b10dcc6-8a99-4ed6-a0cc-7f013adf66c1

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerLevelMorphism
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerLevelFunctionField
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalGluedForgetLevel_dominant
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalGluedForgetLevel_finite


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (h4N : 4 ∣ N)
    (hN : 0 < N) (hM : 0 < M) :
    Function.Surjective (lpsOriginalIntegerNormalGluedForgetLevel N M hNM h4N hN hM) := by
  let := lpsOriginalIntegerNormalGluedForgetLevel_finite N M hNM h4N hN hM
  let := lpsOriginalIntegerNormalGluedForgetLevel_dominant N M hNM h4N hN hM
  let f := lpsOriginalIntegerNormalGluedForgetLevel N M hNM h4N hN hM
  exact (surjective_of_isDominant_of_isClosed_range f f.isClosedMap.isClosed_range).surj
end QEC.Coding.TannerLiftedProduct
