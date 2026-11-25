-- Prove2me | solution 1 for QnYLeibnizW.single_conjTranspose
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:04:22.750802+00:00
-- url     : https://prove2.me/submissions/dcb7e41b-a228-4f9a-b5ea-fd03bf44ed19

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
theorem _root_.solution (p s : Fin n) :
    (Matrix.single p s (1 : ℂ))ᴴ = Matrix.single s p 1 := by
  ext a b
  simp only [Matrix.conjTranspose_apply, Matrix.single_apply]
  split_ifs <;> first | (exfalso; tauto) | simp
end QnYLeibnizW
