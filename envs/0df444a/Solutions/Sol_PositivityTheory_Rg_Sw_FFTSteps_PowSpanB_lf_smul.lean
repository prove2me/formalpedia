-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.FFTSteps.PowSpanB.lf_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:18:54.249681+00:00
-- url     : https://prove2.me/submissions/53338dc3-fa4b-4468-b53e-16deb8dff428

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
theorem _root_.solution (z : ℂ) (b : Matrix (Fin n) (Fin n) ℂ) : lf ε (z • b) = z • lf ε b := by
  simp only [lf, Matrix.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]
end PositivityTheory.Rg.Sw.FFTSteps.PowSpanB
