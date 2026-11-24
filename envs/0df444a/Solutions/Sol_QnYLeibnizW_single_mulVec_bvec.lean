-- Prove2me | solution 1 for QnYLeibnizW.single_mulVec_bvec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:58:03.581797+00:00
-- url     : https://prove2.me/submissions/874b79ca-29be-48d7-adac-cd64dc1d6520

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
theorem _root_.solution (p s q : Fin n) :
    Matrix.single p s (1 : ℂ) *ᵥ bvec q = if q = s then bvec p else 0 := by
  funext j
  simp only [bvec, Matrix.mulVec_single, Matrix.single_apply, mul_one]
  by_cases h : q = s
  · subst h
    by_cases hj : j = p
    · subst hj
      simp
    · simp [hj, Ne.symm hj, Pi.single_apply]
  · simp [h, Ne.symm h]
end QnYLeibnizW
