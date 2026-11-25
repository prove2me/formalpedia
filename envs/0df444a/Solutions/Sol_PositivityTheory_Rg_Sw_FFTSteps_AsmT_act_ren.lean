-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.FFTSteps.AsmT.act_ren
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:40:24.254395+00:00
-- url     : https://prove2.me/submissions/982c2e5c-55af-46d4-88ca-4a942309ebf4

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyTB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyT
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_AsmT_sum_invE
import Theorems.Thm_P2M_PositivityTheory_Rg_Sw_FFTSteps_AsmT_eval_res__ae91c244e0c8

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
theorem _root_.solution (u : Matrix (Fin (NN ι A B)) (Fin (NN ι A B)) ℂ) (z : (ι × A) ⊕ (ι × B) → ℂ) :
    (act u (u.map star) (fun v => eval z (resφ ι v))) ∘ ren = act (blk u) ((blk u).map star) z := by
  funext v
  rcases v with ⟨i, a⟩ | ⟨i, b⟩
  · simp only [Function.comp, ren, Sum.map_inl, Prod.map, act, Sum.elim_inl, id, eval_resφ]
    exact sum_invE (fun j => u (emb i) j) (fun i' => z (Sum.inl (i', a)))
  · simp only [Function.comp, ren, Sum.map_inr, Prod.map, act, Sum.elim_inr, id, eval_resφ, Matrix.map_apply]
    exact sum_invE (fun j => star (u (emb i) j)) (fun i' => z (Sum.inr (i', b)))
end PositivityTheory.Rg.Sw.FFTSteps.AsmT
