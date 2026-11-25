-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.FFTSteps.AsmA.act_act
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:39:49.848795+00:00
-- url     : https://prove2.me/submissions/220a44d1-6255-4d88-9613-0f137a506f7a

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyTA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory MvPolynomial
open scoped ComplexOrder
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.FFTSteps PositivityTheory.Rg.Sw.FFTSteps.AsmA
variable {ι A B : Type} [Fintype ι]
namespace PositivityTheory.Rg.Sw.FFTSteps.AsmA
theorem _root_.solution (g h g' h' : Matrix ι ι ℂ) (z : (ι × A) ⊕ (ι × B) → ℂ) :
    act g h (act g' h' z) = act (g * g') (h * h') z := by
  funext v
  rcases v with ⟨i, a⟩ | ⟨i, b⟩
  · simp only [act, Sum.elim_inl, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc]
    exact Finset.sum_comm
  · simp only [act, Sum.elim_inr, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc]
    exact Finset.sum_comm
end PositivityTheory.Rg.Sw.FFTSteps.AsmA
