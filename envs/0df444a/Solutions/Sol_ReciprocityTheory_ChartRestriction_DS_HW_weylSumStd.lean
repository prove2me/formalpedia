-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.weylSumStd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:56:52.183533+00:00
-- url     : https://prove2.me/submissions/7943bcac-8060-4028-a96e-2b4229797e27

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_KTypeIntDomStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_WeylPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_WeylRatio
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_BlockSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_WeylVanish
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_WeylSum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_weylSum_inj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_weylSum_shift
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_blockSum_plus
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_weylK_std_vanish


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
theorem _root_.solution : WeylSumStdStatement := by
  intro n ε Λ hint hΛ
  refine ⟨?_, fun s hs => weylK_std_vanish ε Λ hint hΛ s hs⟩
  have h := weylSum_shift ε Λ hΛ 1 fun β => blockSum_plus ε β _ (weylSum_inj hΛ β)
  simpa only [one_smul, stdWt] using h
end ReciprocityTheory.ChartRestriction.DS.HW
