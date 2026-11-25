-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.FFTSteps.integrable_gs_re
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:15:24.185417+00:00
-- url     : https://prove2.me/submissions/706b45e4-373f-4086-ac79-e1786c9bc82c

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_NullTop
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_exp_sum_sum
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_integrable_gs_prod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory MvPolynomial Filter Topology
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.FFTSteps
variable {m n : ℕ}
namespace PositivityTheory.Rg.Sw.FFTSteps
theorem _root_.solution {c : ℝ} (hc : 0 < c) :
    Integrable (fun x : Fin m → Fin n → ℂ => Real.exp (-(c * ∑ a, ∑ i, ‖x a i‖ ^ 2))) := by
  exact (integrable_gs_prod hc).congr (ae_of_all _ fun x => (exp_sum_sum c x).symm)
end PositivityTheory.Rg.Sw.FFTSteps
