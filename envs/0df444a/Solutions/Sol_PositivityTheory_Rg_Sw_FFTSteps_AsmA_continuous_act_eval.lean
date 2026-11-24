-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.FFTSteps.AsmA.continuous_act_eval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:14:03.084212+00:00
-- url     : https://prove2.me/submissions/cd82580c-d0b5-4620-a7cf-ab211be53fe6

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
theorem _root_.solution {X : Type} [TopologicalSpace X] {F G : X → Matrix ι ι ℂ} (hF : Continuous F)
    (hG : Continuous G) (z : (ι × A) ⊕ (ι × B) → ℂ) (p : PV ι A B) :
    Continuous fun x => eval (act (F x) (G x) z) p := by
  refine (MvPolynomial.continuous_eval p).comp (continuous_pi fun v => ?_)
  rcases v with ⟨i, a⟩ | ⟨i, b⟩
  · simp only [act, Sum.elim_inl]
    exact continuous_finsetSum _ fun j _ => (hF.matrix_elem i j).mul continuous_const
  · simp only [act, Sum.elim_inr]
    exact continuous_finsetSum _ fun j _ => (hG.matrix_elem i j).mul continuous_const
end PositivityTheory.Rg.Sw.FFTSteps.AsmA
