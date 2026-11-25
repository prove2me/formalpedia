-- Prove2me | solution 1 for P2M_PositivityTheory_Rg_Sw_FFTSteps_differentiable_eval__68dfac1aeb37
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:55:20.90652+00:00
-- url     : https://prove2.me/submissions/977dddb5-8648-49b3-98cc-6a776457b892

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_ExistsUnitaryDiagonalUnitary

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Matrix Complex Filter Topology
open scoped ComplexConjugate ComplexOrder
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.FFTSteps
variable {ι A B : Type} [Fintype ι] [DecidableEq ι]
namespace PositivityTheory.Rg.Sw.FFTSteps
theorem _root_.solution {σ : Type} (p : MvPolynomial σ ℂ) (f : ℂ → σ → ℂ)
    (hf : ∀ v, Differentiable ℂ (fun c => f c v)) :
    Differentiable ℂ (fun c => MvPolynomial.eval (f c) p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
    simp only [map_add]
    exact hp.add hq
  | mul_X p v hp =>
    simp only [map_mul, MvPolynomial.eval_X]
    exact hp.mul (hf v)
end PositivityTheory.Rg.Sw.FFTSteps
