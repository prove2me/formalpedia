-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.FFTSteps.PosProof.continuous_hk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:38:17.262428+00:00
-- url     : https://prove2.me/submissions/46bbc87e-ad35-4282-a1a8-3b74b894c573

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
theorem _root_.solution (k l : ℕ) : Continuous (hk k l) := by
  unfold hk e1
  fun_prop
end PositivityTheory.Rg.Sw.FFTSteps.PosProof
