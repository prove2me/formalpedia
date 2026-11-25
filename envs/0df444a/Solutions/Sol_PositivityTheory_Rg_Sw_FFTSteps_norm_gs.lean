-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.FFTSteps.norm_gs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:39:07.714088+00:00
-- url     : https://prove2.me/submissions/8b5dcb8c-49ec-4d75-b0a9-dbb4015f6853

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_NullTop
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_gs_eq

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
theorem _root_.solution (c : ℝ) (x : Fin m → Fin n → ℂ) :
    ‖gs c x‖ = Real.exp (-(c * ∑ a, ∑ i, ‖x a i‖ ^ 2)) := by
  rw [gs_eq, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
end PositivityTheory.Rg.Sw.FFTSteps
