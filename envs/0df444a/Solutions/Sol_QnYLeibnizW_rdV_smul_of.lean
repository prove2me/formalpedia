-- Prove2me | solution 1 for QnYLeibnizW.rdV_smul_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:05:10.81085+00:00
-- url     : https://prove2.me/submissions/163593b8-3795-4ef7-ba6b-82f4402846e4

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ConjugateTransposeLeibniz_ExpMulVecFix
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ConjugateTransposeLeibniz_YOperatorLeibnizRule
import Theorems.Thm_QnYLeibnizW_curve_zero
import Theorems.Thm_QnYLeibnizW_rdV_of_hasDerivAt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ContDiff
noncomputable section
open QnYLeibnizW
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace QnYLeibnizW
theorem _root_.solution {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (X g : Matrix (Fin n) (Fin n) ℂ) (φ : Matrix (Fin n) (Fin n) ℂ → ℂ) (f : Matrix (Fin n) (Fin n) ℂ → E)
    (d : ℂ) (L : E)
    (hφ : HasDerivAt (fun t : ℝ => φ (g * NormedSpace.exp ((t : ℂ) • X))) d 0)
    (hf : HasDerivAt (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) L 0) :
    RdV X (fun x => φ x • f x) g = φ g • L + d • f g := by
  apply rdV_of_hasDerivAt
  have h := hφ.smul hf
  simp only [curve_zero] at h
  exact h
end QnYLeibnizW
