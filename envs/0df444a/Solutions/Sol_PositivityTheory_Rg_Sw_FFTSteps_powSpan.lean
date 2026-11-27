-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.FFTSteps.powSpan
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:28:43.604219+00:00
-- url     : https://prove2.me/submissions/80011d69-6e9c-4ced-9d14-5d466852d143

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyAlt
import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_PowSpan
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_PowSpanB_span_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.FFTSteps
namespace PositivityTheory.Rg.Sw.FFTSteps
theorem _root_.solution : PowSpan := fun _ _ ε => PowSpanB.span_eq ε
end PositivityTheory.Rg.Sw.FFTSteps
