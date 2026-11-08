-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalSpecialFibre_fieldPullback_reduced
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:28:01.605713+00:00
-- url     : https://prove2.me/submissions/769d2f8d-9206-4771-a86f-d0b3b688d47f

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_PrimeReducedBaseChange
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalReducedSpecialFiber
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGeometricallyReducedSpecialFiber
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalSpecialFibreToPrimeField_geometricallyReduced

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (p : ℕ) [Fact p.Prime] (N : ℕ) [NeZero N] (hN : 0 < N)
    (hpN : ¬ p ∣ N) (K : Type) [Field K]
    (g : Spec (.of K) ⟶ Spec (.of (ZMod p))) :
    _root_.AlgebraicGeometry.IsReduced
      (pullback (lpsOriginalSpecialFibreToPrimeField p N hN) g) := by
  let := lpsOriginalSpecialFibreToPrimeField_geometricallyReduced p N hN hpN
  exact GeometricallyReduced.geometrically_isReduced _ _ _ (.of_hasPullback _ _)
end QEC.Coding.TannerLiftedProduct
