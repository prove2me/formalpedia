-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalSpecialFibreFrobenius_j_natural
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:21:35.363773+00:00
-- url     : https://prove2.me/submissions/d6ba0ab7-504f-4c38-bfb6-cd9a4c61e314

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_AbsoluteFrobenius
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerProperModel
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSpecialFibreFrobenius
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_SchemeFrobenius_absoluteFrobenius_natural


set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
open QEC.Coding.AlgebraicGeometry.SchemeFrobenius
variable (p : ℕ) [Fact p.Prime] (N : ℕ) (hN : 0<N)
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution :
    lpsOriginalSpecialFibreFrobenius p N hN ≫ lpsOriginalSpecialFibreToProjectiveJ p N hN =
      lpsOriginalSpecialFibreToProjectiveJ p N hN ≫
        absoluteFrobenius p _ (lpsOriginalProjectiveJSpecialFibreToPrimeField p) :=
  absoluteFrobenius_natural p _ (lpsOriginalSpecialFibreToPrimeField p N hN)
    (lpsOriginalSpecialFibreToProjectiveJ p N hN) (lpsOriginalProjectiveJSpecialFibreToPrimeField p)
end QEC.Coding.TannerLiftedProduct
