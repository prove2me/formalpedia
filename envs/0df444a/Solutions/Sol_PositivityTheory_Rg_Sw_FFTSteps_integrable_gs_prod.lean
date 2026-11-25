-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.FFTSteps.integrable_gs_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:07:44.326477+00:00
-- url     : https://prove2.me/submissions/8556f777-59ed-4853-b19c-1e04d17cde46

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_NullTop
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_integrable_gs_row

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
set_option maxHeartbeats 1000000
namespace PositivityTheory.Rg.Sw.FFTSteps
theorem _root_.solution {c : ℝ} (hc : 0 < c) :
    Integrable (fun x : Fin m → Fin n → ℂ => ∏ a, ∏ i, Real.exp (-(c * ‖x a i‖ ^ 2))) := by
  have h := Integrable.fintype_prod (ι := Fin m) (E := Fin n → ℂ) (μ := fun _ => (volume : Measure (Fin n → ℂ)))
    (f := fun _ y => ∏ i, Real.exp (-(c * ‖y i‖ ^ 2))) (fun _ => integrable_gs_row hc)
  exact h
end PositivityTheory.Rg.Sw.FFTSteps
