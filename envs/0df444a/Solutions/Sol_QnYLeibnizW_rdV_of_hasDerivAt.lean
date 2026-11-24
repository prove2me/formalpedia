-- Prove2me | solution 1 for QnYLeibnizW.rdV_of_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:58:02.543651+00:00
-- url     : https://prove2.me/submissions/82eed7d8-ceda-4580-83ff-66f444bd4ff7

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ConjugateTransposeLeibniz_ExpMulVecFix
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ConjugateTransposeLeibniz_YOperatorLeibnizRule

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
    (X g : Matrix (Fin n) (Fin n) ℂ) (f : Matrix (Fin n) (Fin n) ℂ → E) (L : E)
    (hf : HasDerivAt (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) L 0) : RdV X f g = L := by
  exact hf.deriv
end QnYLeibnizW
