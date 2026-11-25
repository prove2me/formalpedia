-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.FFTSteps.AsmT.eval_Tf_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:23:29.692588+00:00
-- url     : https://prove2.me/submissions/82480240-6791-4948-bcf5-6c06c362ce60

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyT
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_Assembly
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_AsmA_ext_all
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_AsmT_eval_Tf


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
open scoped ComplexOrder Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.FFTSteps PositivityTheory.Rg.Sw.FFTSteps.AsmT
open AsmA
attribute [local irreducible] Tf
variable {ι A B : Type} [Fintype ι] [DecidableEq ι] [Fintype A] [Fintype B]
namespace PositivityTheory.Rg.Sw.FFTSteps.AsmT
theorem _root_.solution (hE : Ext) (hA : Avg) {q : PV ι A B} (hq : IsInv q) (z : (ι × A) ⊕ (ι × B) → ℂ) :
    eval z (Tf hA q) = ∫ k, eval (act 1 (Mk (ι := ι) (A := A) (B := B) k) z) q ∂(Formalism.REAL.muK (fun _ : Fin (NN ι A B) => true)) := by
  rw [eval_Tf]
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  exact ext_all hE hq _ z
end PositivityTheory.Rg.Sw.FFTSteps.AsmT
