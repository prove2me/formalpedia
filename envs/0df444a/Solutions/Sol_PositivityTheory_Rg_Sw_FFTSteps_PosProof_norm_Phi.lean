-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.FFTSteps.PosProof.norm_Phi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:49:33.345032+00:00
-- url     : https://prove2.me/submissions/64473f99-af3c-4303-914f-19bf893b887e

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_IntegralHkDiag
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_ContinuousPhi
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_PosProof_unitary_norm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory MvPolynomial Module
open scoped ComplexConjugate
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.FFTSteps PositivityTheory.Rg.Sw.FFTSteps.PosProof
variable {ι A B : Type} [Fintype ι] [DecidableEq ι] [Fintype A] [Fintype B]
namespace PositivityTheory.Rg.Sw.FFTSteps.PosProof
theorem _root_.solution (U : Matrix ι ι ℂ) (hU : star U * U = 1) (z : Sg ι A B → ℂ) :
    ∑ s, ‖Phi U z s‖ ^ 2 = ∑ s, ‖z s‖ ^ 2 := by
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  congr 1
  rw [Fintype.sum_prod_type_right, Fintype.sum_prod_type_right]
  refine Finset.sum_congr rfl fun b _ => ?_
  exact unitary_norm U hU fun j => z (Sum.inr (j, b))
end PositivityTheory.Rg.Sw.FFTSteps.PosProof
