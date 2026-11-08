-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalSpecialFibreFrobenius_stalk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:19:24.797245+00:00
-- url     : https://prove2.me/submissions/29cb72d6-b33e-4914-9267-0d1d96dbbc1c

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_AbsoluteFrobenius
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerProperModel
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSpecialFibreFrobenius
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_SchemeFrobenius_absoluteFrobenius_stalk_apply


set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
open QEC.Coding.AlgebraicGeometry.SchemeFrobenius
variable (p : ℕ) [Fact p.Prime] (N : ℕ) (hN : 0<N)
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (x : lpsOriginalSpecialFibre p N hN)
    (s : (lpsOriginalSpecialFibre p N hN).presheaf.stalk x) :
    (lpsOriginalSpecialFibreFrobenius p N hN).stalkMap x s = s^p :=
  absoluteFrobenius_stalk_apply p _ (lpsOriginalSpecialFibreToPrimeField p N hN) x s
end QEC.Coding.TannerLiftedProduct
