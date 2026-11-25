-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.FFTSteps.PosProof.integral_mon_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:13:33.046676+00:00
-- url     : https://prove2.me/submissions/4fa346db-bd08-4cd5-9d4f-34969392b9ff

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_ContinuousPhi
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_IntegralMonSelf
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_PosProof_integral_mon
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_PosProof_integral_hk_diag


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
theorem _root_.solution (m : Sg ι A B →₀ ℕ) :
    ∫ z : Sg ι A B → ℂ, mon m z * star (mon m z) * Complex.exp (-(∑ s, ‖z s‖ ^ 2 : ℝ)) =
      ((∏ s, jr (m s) : ℝ) : ℂ) := by
  rw [integral_mon]
  push_cast
  exact Finset.prod_congr rfl fun s _ => integral_hk_diag _
end PositivityTheory.Rg.Sw.FFTSteps.PosProof
