-- Prove2me | solution 1 for P2M_PositivityTheory_Rg_Sw_FFTSteps_AsmT_eval_res__ae91c244e0c8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:29:34.356334+00:00
-- url     : https://prove2.me/submissions/181e160a-9354-4603-9c9b-a9f72a101650

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyTB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyT

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.FFTSteps PositivityTheory.Rg.Sw.FFTSteps.AsmT
open AsmA
variable {ι A B : Type} [Fintype ι] [DecidableEq ι] [Fintype A] [Fintype B]
namespace PositivityTheory.Rg.Sw.FFTSteps.AsmT
theorem _root_.solution (z : (ι × A) ⊕ (ι × B) → ℂ) (v : (Fin (NN ι A B) × A) ⊕ (Fin (NN ι A B) × B)) :
    eval z (resφ ι v) = Sum.elim (fun x : Fin (NN ι A B) × A => (invE A B x.1).elim 0 fun i => z (Sum.inl (i, x.2)))
      (fun y : Fin (NN ι A B) × B => (invE A B y.1).elim 0 fun i => z (Sum.inr (i, y.2))) v := by
  rcases v with ⟨j, a⟩ | ⟨j, b⟩ <;> cases h : invE A B j <;> simp [resφ, h]
end PositivityTheory.Rg.Sw.FFTSteps.AsmT
