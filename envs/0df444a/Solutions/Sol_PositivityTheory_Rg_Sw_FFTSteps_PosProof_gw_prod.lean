-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.FFTSteps.PosProof.gw_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:38:19.629839+00:00
-- url     : https://prove2.me/submissions/6b5392a4-a301-41b4-ac61-bede9d788f51

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_ContinuousPhi
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_IntegralMonSelf

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
theorem _root_.solution (z : Sg ι A B → ℂ) : Complex.exp (-(∑ s, ‖z s‖ ^ 2 : ℝ)) = ∏ s, e1 (z s) := by
  simp only [e1]
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  simp [Finset.sum_neg_distrib]
end PositivityTheory.Rg.Sw.FFTSteps.PosProof
