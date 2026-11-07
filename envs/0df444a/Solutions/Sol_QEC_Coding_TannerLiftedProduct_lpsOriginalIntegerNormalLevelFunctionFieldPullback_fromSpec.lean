-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalLevelFunctionFieldPullback_fromSpec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:31:25.295188+00:00
-- url     : https://prove2.me/submissions/6d6195f2-3a5d-4128-bc65-ec3cb7659bc0

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerLevelMorphism
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerLevelFunctionField
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGenericStalkMap_fromSpec

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
noncomputable section
universe u
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (h4N : 4 ∣ N)
    (hN : 0 < N) (hM : 0 < M) :
    letI := lpsOriginalIntegerNormalGluedScheme_integral N hN
    letI := lpsOriginalIntegerNormalGluedScheme_integral M hM
    Spec.map (CommRingCat.ofHom
      (lpsOriginalIntegerNormalLevelFunctionFieldPullback N M hNM h4N hN hM)) ≫
      (lpsOriginalIntegerNormalGluedScheme N hN).fromSpecStalk
        (genericPoint (lpsOriginalIntegerNormalGluedScheme N hN)) =
      (lpsOriginalIntegerNormalGluedScheme M hM).fromSpecStalk
        (genericPoint (lpsOriginalIntegerNormalGluedScheme M hM)) ≫
          lpsOriginalIntegerNormalGluedForgetLevel N M hNM h4N hN hM := by
  let := lpsOriginalIntegerNormalGluedScheme_integral N hN
  let := lpsOriginalIntegerNormalGluedScheme_integral M hM
  exact lpsOriginalGenericStalkMap_fromSpec
    (lpsOriginalIntegerNormalGluedForgetLevel N M hNM h4N hN hM)
    (genericPoint (lpsOriginalIntegerNormalGluedScheme M hM))
    (genericPoint (lpsOriginalIntegerNormalGluedScheme N hN))
    (lpsOriginalIntegerNormalGluedForgetLevel_generic N M hNM h4N hN hM)
end QEC.Coding.TannerLiftedProduct
