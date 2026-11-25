-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.whittakerZeroStatement
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:44:09.4426+00:00
-- url     : https://prove2.me/submissions/104d84cf-a83b-455a-a908-cfb7b0c4854d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_Central
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_Tensor
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_CapelliWhittakerZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_WhittakerZeroStatement
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_capelli_whittaker_zero


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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
open ReciprocityTheory.ChartRestriction.DS
universe u v
namespace ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
theorem _root_.solution : WhittakerZeroStatement.{u, v} := by
  intro M R _ _ _ _ k E D l x hD
  exact capelli_whittaker_zero k E D l x hD
end ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
