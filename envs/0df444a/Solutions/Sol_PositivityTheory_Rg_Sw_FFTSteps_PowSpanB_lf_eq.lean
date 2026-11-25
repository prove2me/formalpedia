-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.FFTSteps.PowSpanB.lf_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:40:48.480617+00:00
-- url     : https://prove2.me/submissions/9a3a6318-fd78-4a6f-8953-5ab66f3ffda9

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
theorem _root_.solution (b : Matrix (Fin n) (Fin n) ℂ) :
    (∑ i, ∑ j, C (b i j) * (Qp ε j i : PX m n)) = lf ε b := by
  simp only [lf, C_mul']
end PositivityTheory.Rg.Sw.FFTSteps.PowSpanB
