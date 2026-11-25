-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.FFTSteps.AsmT.Tf_deg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:16:08.999882+00:00
-- url     : https://prove2.me/submissions/2b948150-40e1-4e97-9138-abb370671ddf

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyTB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyT
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_AsmA_totalDegree_aeval_le


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
theorem _root_.solution (hA : Avg) (q : PV ι A B) : (Tf hA q).totalDegree ≤ q.totalDegree := by
  have hs := Classical.choose_spec (hA (NN ι A B) A B (rename ren q))
  refine (totalDegree_aeval_le _ (fun v => ?_) _).trans (hs.2.1.trans (totalDegree_rename_le _ _))
  rcases v with ⟨j, a⟩ | ⟨j, b⟩
  · simp only [resφ, Sum.elim_inl]
    cases h : invE A B j <;> simp [Option.elim, totalDegree_X]
  · simp only [resφ, Sum.elim_inr]
    cases h : invE A B j <;> simp [Option.elim, totalDegree_X]
end PositivityTheory.Rg.Sw.FFTSteps.AsmT
