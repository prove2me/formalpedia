-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.FFTSteps.PosProof.Phi_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:30:40.731149+00:00
-- url     : https://prove2.me/submissions/2847dfaf-a90d-4d38-b5c9-359579ab5825

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_IntegralHkDiag
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_ContinuousPhi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory MvPolynomial Module
open scoped ComplexConjugate
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.FFTSteps PositivityTheory.Rg.Sw.FFTSteps.PosProof
variable {ι A B : Type} [Fintype ι] [DecidableEq ι] [Fintype A] [Fintype B]
namespace PositivityTheory.Rg.Sw.FFTSteps.PosProof
theorem _root_.solution (z : Sg ι A B → ℂ) : Phi 1 z = z := by
  funext s
  rcases s with x | ⟨i, b⟩
  · rfl
  · simp [Phi, Matrix.one_apply]
end PositivityTheory.Rg.Sw.FFTSteps.PosProof
