-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.FFTSteps.AsmA.sub_one_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:48:51.507381+00:00
-- url     : https://prove2.me/submissions/5b0f4d1b-9e70-43f1-90d1-29f3234081bb

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyTA
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_AsmA_eval_sub
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_AsmA_act_one_one

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
theorem _root_.solution [DecidableEq ι] (p : PV ι A B) : sub (1 : Matrix ι ι ℂ) 1 p = p := by
  apply MvPolynomial.funext
  intro z
  rw [eval_sub, act_one_one]
end PositivityTheory.Rg.Sw.FFTSteps.AsmA
