-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalSpecialFibreHeckePair_snd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:09:48.189523+00:00
-- url     : https://prove2.me/submissions/d0f84a09-f528-40f3-bc98-8af264fc3d51

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
    lpsOriginalSpecialFibreHeckePair l N M hNM h4N hN hM ≫ pullback.snd
      (lpsOriginalSpecialFibreToPrimeField l N hN) (lpsOriginalSpecialFibreToPrimeField l N hN) =
    lpsOriginalSpecialFibreSecondLevelMap l N M hNM h4N hN hM :=
  pullback.lift_snd _ _ _
end QEC.Coding.TannerLiftedProduct
