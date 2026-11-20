-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalSpecialFibreHeckePair_finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:24:59.236175+00:00
-- url     : https://prove2.me/submissions/c989ea0b-b3e0-481e-bd66-6b2723a07dae

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSecondIntegerHecke
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSpecialFibreFrobenius
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSpecialHecke
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalSpecialFibreForgetLevel_finite
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalSpecialFibreToPrimeField_proper
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalSpecialFibreHeckePair_fst

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open QEC.Coding.AlgebraicGeometry.SchemeFrobenius
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (l N M : ℕ) [Fact l.Prime] [NeZero N] [NeZero M]
    (hNM : N ∣ M) (h4N : 4 ∣ N) (hN : 0 < N) (hM : 0 < M) :
    IsFinite (lpsOriginalSpecialFibreHeckePair l N M hNM h4N hN hM) := by
  let : IsProper (lpsOriginalSpecialFibreToPrimeField l N hN) :=
    lpsOriginalSpecialFibreToPrimeField_proper l N hN
  let : IsFinite (lpsOriginalSpecialFibreHeckePair l N M hNM h4N hN hM ≫ pullback.fst
      (lpsOriginalSpecialFibreToPrimeField l N hN) (lpsOriginalSpecialFibreToPrimeField l N hN)) := by
    rw [lpsOriginalSpecialFibreHeckePair_fst]
    exact lpsOriginalSpecialFibreForgetLevel_finite l N M hNM h4N hN hM
  exact IsFinite.of_comp (lpsOriginalSpecialFibreHeckePair l N M hNM h4N hN hM)
    (pullback.fst (lpsOriginalSpecialFibreToPrimeField l N hN)
      (lpsOriginalSpecialFibreToPrimeField l N hN))
end QEC.Coding.TannerLiftedProduct
