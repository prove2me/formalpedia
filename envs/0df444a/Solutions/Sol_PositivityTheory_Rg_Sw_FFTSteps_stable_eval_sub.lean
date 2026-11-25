-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.FFTSteps.stable_eval_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:39:22.372195+00:00
-- url     : https://prove2.me/submissions/cf3b52a5-5271-47b6-9e5e-3c79d93ccb37

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyAlt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_InvariantPolynomialEqAevalPairings
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_Stable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.FFTSteps
namespace PositivityTheory.Rg.Sw.FFTSteps
theorem _root_.solution {ι A B : Type} [Fintype ι] (g h : Matrix ι ι ℂ) (z : (ι × A) ⊕ (ι × B) → ℂ) (p : PV ι A B) :
    eval z (sub g h p) = eval (Sum.elim (fun x : ι × A => ∑ j, g x.1 j * z (Sum.inl (j, x.2)))
      (fun y : ι × B => ∑ j, h y.1 j * z (Sum.inr (j, y.2)))) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [sub]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, sub, aeval_X, eval_X]
    congr 1
    rcases v with x | y <;> simp [map_sum]
end PositivityTheory.Rg.Sw.FFTSteps
