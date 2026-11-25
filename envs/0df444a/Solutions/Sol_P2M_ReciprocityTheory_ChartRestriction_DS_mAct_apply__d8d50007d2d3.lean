-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_DS_mAct_apply__d8d50007d2d3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:52:12.305741+00:00
-- url     : https://prove2.me/submissions/da0ec208-dbaa-4d8b-a5df-3b2dfd7f8620

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_Permute
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_LayerBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_PositionPrependMemNoncompactPositionSubmodule

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (k : ℕ) (a b : Fin n) (F : Big n k M) (κ : Fin k → Fin n × Fin n) :
    mAct E k a b F κ = E a b (F κ) := rfl
end ReciprocityTheory.ChartRestriction.DS
