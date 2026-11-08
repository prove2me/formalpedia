-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalSpecialFibreFrobenius_overPrimeField
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:20:42.196243+00:00
-- url     : https://prove2.me/submissions/5ec3db6d-0a64-49fc-950c-0a424cd3b1be

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_AbsoluteFrobenius
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerProperModel
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSpecialFibreFrobenius
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_SchemeFrobenius_absoluteFrobenius_overPrimeField


set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
open QEC.Coding.AlgebraicGeometry.SchemeFrobenius
variable (p : ℕ) [Fact p.Prime] (N : ℕ) (hN : 0<N)
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution :
    lpsOriginalSpecialFibreFrobenius p N hN ≫ lpsOriginalSpecialFibreToPrimeField p N hN =
      lpsOriginalSpecialFibreToPrimeField p N hN :=
  absoluteFrobenius_overPrimeField p _ (lpsOriginalSpecialFibreToPrimeField p N hN)
end QEC.Coding.TannerLiftedProduct
