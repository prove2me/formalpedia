-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.FFTSteps.PosProof.Phi_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:44:10.092534+00:00
-- url     : https://prove2.me/submissions/7bdcb75d-4654-4fb6-aa0f-13e8e9ff69df

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_ContinuousPhi
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_IntegralMonSelf

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
theorem _root_.solution (d : ι → ℝ) (z : Sg ι A B → ℂ) :
    Phi (Matrix.diagonal fun i => (d i : ℂ)) z = fun s => (kap d s : ℂ) * z s := by
  funext s
  rcases s with x | ⟨i, b⟩
  · simp [Phi, kap]
  · simp [Phi, kap, Matrix.diagonal_apply]
end PositivityTheory.Rg.Sw.FFTSteps.PosProof
