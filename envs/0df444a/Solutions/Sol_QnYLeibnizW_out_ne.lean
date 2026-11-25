-- Prove2me | solution 1 for QnYLeibnizW.out_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:04:21.819586+00:00
-- url     : https://prove2.me/submissions/608ae882-0ec0-44b7-a048-7d824bfdc9d3

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ConjugateTransposeLeibniz_ExpMulVecFix
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ConjugateTransposeLeibniz_YOperatorLeibnizRule
import Theorems.Thm_QnYLeibnizW_posL_val

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
variable {k r : ℕ} {i : Fin (r + 1)}
namespace QnYLeibnizW
theorem _root_.solution (p : Fin (mdim k r i)) (q : Fin (2 * r + k + 1))
    (hq : q.val < i.val ∨ 2 * r + k < q.val + i.val) :
    q ≠ posL k r i p ∧ q ≠ GBasic.sig k r (posL k r i p) := by
  have hp := p.isLt
  have hi := i.isLt
  unfold mdim at hp
  constructor
  · intro h
    have h2 := congrArg Fin.val h
    rw [posL_val] at h2
    omega
  · intro h
    have h2 := congrArg Fin.val h
    unfold GBasic.sig at h2
    split_ifs at h2 with hc
    · simp only [posL_val] at h2 hc
      omega
    · rw [posL_val] at h2
      omega
end QnYLeibnizW
