-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.FFTSteps.PowSpanB.lf_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:18:53.22242+00:00
-- url     : https://prove2.me/submissions/4e40a486-43f7-4bc8-bcfb-2ff21c135e0b

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyAlt
import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_PowSpan

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
open PositivityTheory.Rg.Sw.FFTSteps.PowSpanB
variable {m n : ℕ} (ε : Fin m → Bool)
namespace PositivityTheory.Rg.Sw.FFTSteps.PowSpanB
theorem _root_.solution (b c : Matrix (Fin n) (Fin n) ℂ) : lf ε (b + c) = lf ε b + lf ε c := by
  simp only [lf, Matrix.add_apply, add_smul, Finset.sum_add_distrib]
end PositivityTheory.Rg.Sw.FFTSteps.PowSpanB
