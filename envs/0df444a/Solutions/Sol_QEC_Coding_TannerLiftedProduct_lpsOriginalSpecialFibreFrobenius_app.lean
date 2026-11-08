-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalSpecialFibreFrobenius_app
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:20:40.573306+00:00
-- url     : https://prove2.me/submissions/e3b297a8-6c00-4458-b0b2-fd2dcfc8a282

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_AbsoluteFrobenius
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerProperModel
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSpecialFibreFrobenius
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_SchemeFrobenius_absoluteFrobenius_app_apply


set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
open QEC.Coding.AlgebraicGeometry.SchemeFrobenius
variable (p : ℕ) [Fact p.Prime] (N : ℕ) (hN : 0<N)
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (U : (lpsOriginalSpecialFibre p N hN).Opens)
    (s : Γ(lpsOriginalSpecialFibre p N hN, U)) :
    (lpsOriginalSpecialFibreFrobenius p N hN).app U s = s^p :=
  absoluteFrobenius_app_apply p _ (lpsOriginalSpecialFibreToPrimeField p N hN) U s
end QEC.Coding.TannerLiftedProduct
