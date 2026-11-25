-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.FFTSteps.gs_half
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:41:13.920884+00:00
-- url     : https://prove2.me/submissions/3c9868a5-556f-4e82-a2be-1e7c720cdf8a

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
theorem _root_.solution (c : ℝ) (x : Fin m → Fin n → ℂ) : gs c x = gs (c / 2) x * gs (c / 2) x := by
  simp only [gs, ← Complex.exp_add]
  congr 1
  push_cast
  ring
end PositivityTheory.Rg.Sw.FFTSteps
