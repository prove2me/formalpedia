-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.mexp_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:35:19.912862+00:00
-- url     : https://prove2.me/submissions/4f87e35c-aaa0-42e0-bcfe-589c2863c112

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ModelDer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_InhabA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ModelFun

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
theorem _root_.solution (ε : Fin n → Bool) {m : Fin n → ℤ} (hm : NonnegDom ε m) (a : Fin n) : 0 ≤ mexp ε m a := by
  unfold mexp
  split_ifs with h
  · have hb := (Finset.mem_filter.1 (Finset.min'_mem _ h)).2
    exact sub_nonneg.2 (hm.1 a _ hb.1 hb.2.symm)
  · exact hm.2 a
end ReciprocityTheory.ChartRestriction.DS.HW
