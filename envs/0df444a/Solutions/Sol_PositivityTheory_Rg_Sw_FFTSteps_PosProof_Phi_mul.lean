-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.FFTSteps.PosProof.Phi_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:30:39.64648+00:00
-- url     : https://prove2.me/submissions/94c54eb3-9c52-42ef-ab9e-211dc44bdcb2

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
theorem _root_.solution (g h : Matrix ι ι ℂ) (z : Sg ι A B → ℂ) : Phi (g * h) z = Phi g (Phi h z) := by
  funext s
  rcases s with x | ⟨i, b⟩
  · rfl
  · simp only [Phi, Sum.elim_inr, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]
    exact Finset.sum_comm
end PositivityTheory.Rg.Sw.FFTSteps.PosProof
