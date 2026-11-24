-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.FFTSteps.gs_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:14:07.7731+00:00
-- url     : https://prove2.me/submissions/b37e4f31-6fa0-4c70-a17d-b9aa4bf38b34

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_NullTop

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
    gs c x = ((Real.exp (-(c * ∑ a, ∑ i, ‖x a i‖ ^ 2)) : ℝ) : ℂ) := by
  unfold gs
  rw [Complex.ofReal_exp, Complex.ofReal_neg]
end PositivityTheory.Rg.Sw.FFTSteps
