-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.FFTSteps.AsmT.eval_Tf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:54:33.271809+00:00
-- url     : https://prove2.me/submissions/0265c1b2-1e4d-4d4e-a168-c4a8c9d0d2e8

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyTB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyT
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_AsmT_act_ren
import Theorems.Thm_P2M_PositivityTheory_Rg_Sw_FFTSteps_AsmA_eval_aeval__5549e8dcdd1c
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_AsmA_eval_sub


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
theorem _root_.solution (hA : Avg) (q : PV ι A B) (z : (ι × A) ⊕ (ι × B) → ℂ) :
    eval z (Tf hA q) = ∫ k : Formalism.REAL.KG (fun _ : Fin (NN ι A B) => true),
      eval (act (blk (Formalism.REAL.toMK k)) ((blk (Formalism.REAL.toMK k)).map star) z) q
        ∂(Formalism.REAL.muK (fun _ : Fin (NN ι A B) => true)) := by
  have hs := Classical.choose_spec (hA (NN ι A B) A B (rename ren q))
  rw [Tf, res, eval_aeval', hs.2.2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  simp only
  rw [AsmA.eval_sub, eval_rename, act_ren]
end PositivityTheory.Rg.Sw.FFTSteps.AsmT
