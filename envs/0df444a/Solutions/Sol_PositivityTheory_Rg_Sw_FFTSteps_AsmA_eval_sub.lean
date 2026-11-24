-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.FFTSteps.AsmA.eval_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:30:52.304477+00:00
-- url     : https://prove2.me/submissions/06d45be4-2b9c-4deb-8e21-ed790b146055

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyTA
import Theorems.Thm_P2M_PositivityTheory_Rg_Sw_FFTSteps_AsmA_eval_aeval__5549e8dcdd1c

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
theorem _root_.solution (g h : Matrix ι ι ℂ) (z : (ι × A) ⊕ (ι × B) → ℂ) (p : PV ι A B) :
    eval z (sub g h p) = eval (act g h z) p := by
  unfold sub
  rw [eval_aeval']
  have e : (fun v => eval z (Sum.elim (fun x : ι × A => ∑ j, C (g x.1 j) * (X (Sum.inl (j, x.2)) : PV ι A B))
      (fun y : ι × B => ∑ j, C (h y.1 j) * X (Sum.inr (j, y.2))) v)) = act g h z := by
    funext v
    rcases v with ⟨i, a⟩ | ⟨i, b⟩ <;> simp [act, map_sum]
  rw [e]
end PositivityTheory.Rg.Sw.FFTSteps.AsmA
