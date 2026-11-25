-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.rtr_polyK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:46:09.48761+00:00
-- url     : https://prove2.me/submissions/a3f1c95d-a168-4557-b9da-3a499fa1d6ac

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ModelFun
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_KFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_InhabA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ModelSpace
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_rtr_evalK
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_totalDegree_rsub
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_HW_totalDegree_bind__le_e8e4d4bd1303

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
    rtr ε k (evalK ε Q) ∈ polyK ε Q.totalDegree := by
  rw [rtr_evalK]
  exact Submodule.mem_map_of_mem ((MvPolynomial.mem_restrictTotalDegree ..).mpr
    (totalDegree_bind₁_le _ (totalDegree_rsub ε k) Q))
end ReciprocityTheory.ChartRestriction.DS.HW
