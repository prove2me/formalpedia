-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.totalDegree_rsub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:28:18.689742+00:00
-- url     : https://prove2.me/submissions/7a3dacb4-e898-4864-9530-f1824cdb21b9

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ModelFun
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_KFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_InhabA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ModelSpace

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
theorem _root_.solution (ε : Fin n → Bool) (k : KG ε) (p : Fin n × Fin n) :
    (rsub ε k p).totalDegree ≤ 1 := by
  simp only [rsub]
  refine (MvPolynomial.totalDegree_finset_sum _ _).trans (Finset.sup_le fun l _ => ?_)
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  simp [MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_C]
end ReciprocityTheory.ChartRestriction.DS.HW
