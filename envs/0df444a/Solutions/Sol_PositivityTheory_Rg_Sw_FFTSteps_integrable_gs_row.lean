-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.FFTSteps.integrable_gs_row
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:00:29.308276+00:00
-- url     : https://prove2.me/submissions/ed902d33-f780-40c0-9cae-cf76096ac1bb

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_NullTop
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_integrable_gauss1

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
    Integrable (fun y : Fin n → ℂ => ∏ i, Real.exp (-(c * ‖y i‖ ^ 2))) := by
  exact Integrable.fintype_prod (f := fun _ z => Real.exp (-(c * ‖z‖ ^ 2))) (fun _ => integrable_gauss1 hc)
end PositivityTheory.Rg.Sw.FFTSteps
