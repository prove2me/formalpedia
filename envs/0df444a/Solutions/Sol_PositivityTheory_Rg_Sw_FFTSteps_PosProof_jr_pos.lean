-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.FFTSteps.PosProof.jr_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:03:58.330549+00:00
-- url     : https://prove2.me/submissions/38dcfa4b-bf9c-4c3e-acc9-5e97310242ec

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_IntegralHkDiag
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_PosProof_norm_hk
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_PosProof_integrable_hk

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex Module
open scoped ComplexConjugate
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.FFTSteps PositivityTheory.Rg.Sw.FFTSteps.PosProof
namespace PositivityTheory.Rg.Sw.FFTSteps.PosProof
theorem _root_.solution (k : ℕ) : 0 < jr k := by
  have hint : Integrable (fun z : ℂ => (‖z‖ ^ 2) ^ k * Real.exp (-(‖z‖ ^ 2))) := by
    refine (integrable_hk k k).norm.congr (ae_of_all _ fun z => ?_)
    simp only [norm_hk]
    ring
  have hnn : 0 ≤ fun z : ℂ => (‖z‖ ^ 2) ^ k * Real.exp (-(‖z‖ ^ 2)) := fun z => by positivity
  unfold jr
  rw [integral_pos_iff_support_of_nonneg hnn hint]
  have hc : Continuous fun z : ℂ => (‖z‖ ^ 2) ^ k * Real.exp (-(‖z‖ ^ 2)) := by fun_prop
  exact hc.isOpen_support.measure_pos volume ⟨1, by simp⟩
end PositivityTheory.Rg.Sw.FFTSteps.PosProof
