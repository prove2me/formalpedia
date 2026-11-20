-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalSpecialFibreLift_finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:11:45.356417+00:00
-- url     : https://prove2.me/submissions/033639d6-bfad-4fb0-9fcf-96db1945f902

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSecondIntegerHecke
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSpecialFibreFrobenius
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSpecialHecke
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalSpecialFibreLift_isPullback

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open QEC.Coding.AlgebraicGeometry.SchemeFrobenius
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (l N M : ℕ) [Fact l.Prime]
    (hN : 0 < N) (hM : 0 < M)
    (a : lpsOriginalIntegerNormalGluedScheme M hM ⟶ lpsOriginalIntegerNormalGluedScheme N hN)
    (ha : a ≫ lpsOriginalIntegerNormalGluedToSpecZ N hN =
      lpsOriginalIntegerNormalGluedToSpecZ M hM) (hf : IsFinite a) :
    IsFinite (lpsOriginalSpecialFibreLift l N M hN hM a ha) :=
  (inferInstance : MorphismProperty.IsStableUnderBaseChange @IsFinite).of_isPullback
    (lpsOriginalSpecialFibreLift_isPullback l N M hN hM a ha).flip hf
end QEC.Coding.TannerLiftedProduct
