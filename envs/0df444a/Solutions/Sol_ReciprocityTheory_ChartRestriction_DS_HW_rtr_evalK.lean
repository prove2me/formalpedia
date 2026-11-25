-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.rtr_evalK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:13:51.422195+00:00
-- url     : https://prove2.me/submissions/9bac2cae-a3ef-48f7-aa43-1a2086ad2007

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ModelFun
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_KFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_InhabA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ModelSpace
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_evalK_apply
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_HW_toMK_mul__6ba5f44adf8c

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace ReciprocityTheory.ChartRestriction.DS.HW
theorem _root_.solution (ε : Fin n → Bool) (k : KG ε) (Q : MvPolynomial (Fin n × Fin n) ℂ) :
    rtr ε k (evalK ε Q) = evalK ε (MvPolynomial.bind₁ (rsub ε k) Q) := by
  funext x
  show evalK ε Q (x * k) = evalK ε (MvPolynomial.bind₁ (rsub ε k) Q) x
  rw [evalK_apply, evalK_apply, MvPolynomial.aeval_bind₁]
  refine congrArg (fun g => MvPolynomial.aeval g Q) ?_
  funext p
  simp [rsub, toMK_mul', Matrix.mul_apply]
end ReciprocityTheory.ChartRestriction.DS.HW
