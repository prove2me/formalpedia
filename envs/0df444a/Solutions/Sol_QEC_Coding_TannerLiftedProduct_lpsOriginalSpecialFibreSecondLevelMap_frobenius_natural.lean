-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalSpecialFibreSecondLevelMap_frobenius_natural
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:09:37.453931+00:00
-- url     : https://prove2.me/submissions/1792d3e7-422c-493e-a90d-9caeedf5d37c

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSecondIntegerHecke
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSpecialFibreFrobenius
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSpecialHecke
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_SchemeFrobenius_absoluteFrobenius_natural


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open QEC.Coding.AlgebraicGeometry.SchemeFrobenius
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (l N M : ℕ) [Fact l.Prime] [NeZero N] [NeZero M]
    (hNM : N ∣ M) (h4N : 4 ∣ N) (hN : 0 < N) (hM : 0 < M) :
    lpsOriginalSpecialFibreFrobenius l M hM ≫
      lpsOriginalSpecialFibreSecondLevelMap l N M hNM h4N hN hM =
    lpsOriginalSpecialFibreSecondLevelMap l N M hNM h4N hN hM ≫
      lpsOriginalSpecialFibreFrobenius l N hN :=
  absoluteFrobenius_natural l _ _ _ _
end QEC.Coding.TannerLiftedProduct
