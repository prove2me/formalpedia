-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.FFTSteps.AsmA.totalDegree_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:39:55.662853+00:00
-- url     : https://prove2.me/submissions/7ad6ccc7-527b-4a24-aa3e-d5632d08d0e0

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyTA
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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.FFTSteps PositivityTheory.Rg.Sw.FFTSteps.AsmA
variable {ι A B : Type} [Fintype ι]
namespace PositivityTheory.Rg.Sw.FFTSteps.AsmA
theorem _root_.solution (g h : Matrix ι ι ℂ) (p : PV ι A B) : (sub g h p).totalDegree ≤ p.totalDegree := by
  refine totalDegree_aeval_le _ (fun v => ?_) p
  rcases v with ⟨i, a⟩ | ⟨i, b⟩
  · simp only [Sum.elim_inl]
    refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun j _ => ?_)
    exact (totalDegree_mul _ _).trans (by rw [totalDegree_C, totalDegree_X])
  · simp only [Sum.elim_inr]
    refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun j _ => ?_)
    exact (totalDegree_mul _ _).trans (by rw [totalDegree_C, totalDegree_X])
end PositivityTheory.Rg.Sw.FFTSteps.AsmA
