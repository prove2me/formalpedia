-- Prove2me | solution 1 for P2M_PositivityTheory_Rg_Sw_FFTSteps_AsmA_eval_aeval__5549e8dcdd1c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:14:00.900801+00:00
-- url     : https://prove2.me/submissions/411c5844-69ce-4923-9119-8939a4a86069

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
namespace PositivityTheory.Rg.Sw.FFTSteps.AsmA
theorem _root_.solution {σ τ : Type} (φ : σ → MvPolynomial τ ℂ) (z : τ → ℂ) (p : MvPolynomial σ ℂ) :
    eval z (aeval φ p) = eval (fun v => eval z (φ v)) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp only [aeval_C, MvPolynomial.algebraMap_eq, eval_C]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp => simp only [map_mul, aeval_X, eval_X, hp]
end PositivityTheory.Rg.Sw.FFTSteps.AsmA
