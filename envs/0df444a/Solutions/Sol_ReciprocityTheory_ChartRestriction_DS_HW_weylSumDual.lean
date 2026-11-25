-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.weylSumDual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:40:23.888337+00:00
-- url     : https://prove2.me/submissions/5534dda5-a6ca-4d24-af1d-41ed908d7aa4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_KTypeIntDomStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_WeylPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_WeylRatio
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_BlockSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_WeylVanish
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_WeylSum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_weylSum_inj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_weylSum_shift
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_blockSum_minus
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_weylK_dual_vanish


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
theorem _root_.solution : WeylSumDualStatement := by
  intro n ε Λ hint hΛ
  refine ⟨?_, fun s hs => weylK_dual_vanish ε Λ hint hΛ s hs⟩
  have h := weylSum_shift ε Λ hΛ (-1) fun β => by
    rw [← blockSum_minus ε β _ (weylSum_inj hΛ β)]
    refine Finset.sum_congr rfl fun s _ => Finset.prod_congr rfl fun b _ => by ring
  simpa only [neg_one_smul, dualWt] using h
end ReciprocityTheory.ChartRestriction.DS.HW
