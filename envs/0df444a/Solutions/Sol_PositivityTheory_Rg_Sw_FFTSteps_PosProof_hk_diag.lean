-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.FFTSteps.PosProof.hk_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:14:07.183939+00:00
-- url     : https://prove2.me/submissions/cef216aa-60a5-4357-aacf-a8a57021073e

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
theorem _root_.solution (k : ℕ) (z : ℂ) : hk k k z = (((‖z‖ ^ 2) ^ k * Real.exp (-(‖z‖ ^ 2)) : ℝ) : ℂ) := by
  simp only [hk, e1]
  rw [← mul_pow, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  ring
end PositivityTheory.Rg.Sw.FFTSteps.PosProof
