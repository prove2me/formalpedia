-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalSpecialFibreToPrimeField_geometricallyReduced
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:57:18.764407+00:00
-- url     : https://prove2.me/submissions/ecb961ab-f8d0-43ba-80c5-c06d860533d2

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_PrimeReducedBaseChange
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalReducedSpecialFiber
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGeometricallyReducedSpecialFiber
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_PrimeReducedBaseChange_primeFieldMorphism_geometricallyReduced
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalSpecialFibre_reduced


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (p : ℕ) [Fact p.Prime] (N : ℕ) [NeZero N] (hN : 0 < N)
    (hpN : ¬ p ∣ N) :
    GeometricallyReduced (lpsOriginalSpecialFibreToPrimeField p N hN) := by
  let := lpsOriginalSpecialFibre_reduced N hN p hpN
  exact QEC.Coding.AlgebraicGeometry.PrimeReducedBaseChange.primeFieldMorphism_geometricallyReduced
    p (lpsOriginalSpecialFibre p N hN) (lpsOriginalSpecialFibreToPrimeField p N hN)
end QEC.Coding.TannerLiftedProduct
