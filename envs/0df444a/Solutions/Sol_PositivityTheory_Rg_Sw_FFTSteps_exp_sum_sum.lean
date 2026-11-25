-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.FFTSteps.exp_sum_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:41:12.047512+00:00
-- url     : https://prove2.me/submissions/62688f7c-d6e0-4e0e-b3e9-0156aea7e9e6

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
    Real.exp (-(c * ∑ a, ∑ i, ‖x a i‖ ^ 2)) = ∏ a, ∏ i, Real.exp (-(c * ‖x a i‖ ^ 2)) := by
  simp only [Finset.mul_sum, ← Finset.sum_neg_distrib, Real.exp_sum]
end PositivityTheory.Rg.Sw.FFTSteps
