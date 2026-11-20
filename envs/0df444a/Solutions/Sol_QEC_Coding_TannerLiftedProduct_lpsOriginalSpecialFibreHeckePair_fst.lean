-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalSpecialFibreHeckePair_fst
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:09:34.16702+00:00
-- url     : https://prove2.me/submissions/17f98f5b-bc1c-4ad2-87e6-f147396bc40f

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSecondIntegerHecke
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSpecialFibreFrobenius
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSpecialHecke

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open QEC.Coding.AlgebraicGeometry.SchemeFrobenius
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (l N M : ℕ) [Fact l.Prime] [NeZero N] [NeZero M]
    (hNM : N ∣ M) (h4N : 4 ∣ N) (hN : 0 < N) (hM : 0 < M) :
    lpsOriginalSpecialFibreHeckePair l N M hNM h4N hN hM ≫ pullback.fst
      (lpsOriginalSpecialFibreToPrimeField l N hN) (lpsOriginalSpecialFibreToPrimeField l N hN) =
    lpsOriginalSpecialFibreForgetLevel l N M hNM h4N hN hM :=
  pullback.lift_fst _ _ _
end QEC.Coding.TannerLiftedProduct
