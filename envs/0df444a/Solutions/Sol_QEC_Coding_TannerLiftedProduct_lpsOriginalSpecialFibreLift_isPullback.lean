-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalSpecialFibreLift_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:09:06.685187+00:00
-- url     : https://prove2.me/submissions/5b0cb0bc-62c7-4e87-87b3-e8c30e7e8334

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSecondIntegerHecke
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSpecialFibreFrobenius
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSpecialHecke

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
      lpsOriginalIntegerNormalGluedToSpecZ M hM) :
    IsPullback (lpsOriginalSpecialFibreLift l N M hN hM a ha)
      (pullback.fst (lpsOriginalIntegerNormalGluedToSpecZ M hM) (lpsOriginalPrimeSpecToInteger l))
      (pullback.fst (lpsOriginalIntegerNormalGluedToSpecZ N hN) (lpsOriginalPrimeSpecToInteger l)) a := by
  have outer : IsPullback
      (lpsOriginalSpecialFibreLift l N M hN hM a ha ≫ lpsOriginalSpecialFibreToPrimeField l N hN)
      (pullback.fst (lpsOriginalIntegerNormalGluedToSpecZ M hM) (lpsOriginalPrimeSpecToInteger l))
      (lpsOriginalPrimeSpecToInteger l) (a ≫ lpsOriginalIntegerNormalGluedToSpecZ N hN) := by
    rw [lpsOriginalSpecialFibreLift_overPrimeField, ha]
    exact (IsPullback.of_hasPullback (lpsOriginalIntegerNormalGluedToSpecZ M hM)
      (lpsOriginalPrimeSpecToInteger l)).flip
  exact outer.of_right (lpsOriginalSpecialFibreLift_fst l N M hN hM a ha)
    (IsPullback.of_hasPullback (lpsOriginalIntegerNormalGluedToSpecZ N hN)
      (lpsOriginalPrimeSpecToInteger l)).flip
end QEC.Coding.TannerLiftedProduct
