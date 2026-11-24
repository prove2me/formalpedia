-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.FFTSteps.PosProof.norm_hk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:14:08.247209+00:00
-- url     : https://prove2.me/submissions/6c7d3339-d4e0-4d7f-9029-634b7331d042

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_IntegralHkDiag

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
theorem _root_.solution (k l : ℕ) (z : ℂ) : ‖hk k l z‖ = ‖z‖ ^ (k + l) * Real.exp (-(‖z‖ ^ 2)) := by
  simp only [hk, e1, norm_mul, norm_pow, norm_star, Complex.norm_exp_ofReal, pow_add]
end PositivityTheory.Rg.Sw.FFTSteps.PosProof
