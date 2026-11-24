-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.weylSum_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:58:09.232454+00:00
-- url     : https://prove2.me/submissions/9f255aef-a0c1-4702-9289-e5701d38b80d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_KTypeIntDomStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_WeylPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_WeylRatio
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_BlockSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_WeylVanish
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_WeylSum

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS
namespace ReciprocityTheory.ChartRestriction.DS.HW
theorem _root_.solution {n : ℕ} (ε : Fin n → Bool) (f : Fin n → ℝ) :
    ∑ s, f s = ∑ s ∈ univ.filter (fun s => ε s = true), f s +
      ∑ s ∈ univ.filter (fun s => ε s = false), f s := by
  rw [← Finset.sum_filter_add_sum_filter_not univ (fun s => ε s = true)]
  congr 1
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext s; simp
end ReciprocityTheory.ChartRestriction.DS.HW
