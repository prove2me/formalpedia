-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.FFTSteps.AsmT.integrable_eval_act
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:21:21.099802+00:00
-- url     : https://prove2.me/submissions/53f35409-55c4-47d1-a5ac-cc6ee815f3a6

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyTB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyT
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_AsmA_continuous_act_eval


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
theorem _root_.solution (hA : Avg) (F G : Formalism.REAL.KG (fun _ : Fin (NN ι A B) => true) → Matrix ι ι ℂ)
    (hF : Continuous F) (hG : Continuous G) (z : (ι × A) ⊕ (ι × B) → ℂ) (q : PV ι A B) :
    Integrable (fun k => eval (act (F k) (G k) z) q) (Formalism.REAL.muK (fun _ : Fin (NN ι A B) => true)) :=
  integrableOn_univ.mp ((continuous_act_eval hF hG z q).continuousOn.integrableOn_compact isCompact_univ)
end PositivityTheory.Rg.Sw.FFTSteps.AsmT
