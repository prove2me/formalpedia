-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.capelliTensor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:21:43.9968+00:00
-- url     : https://prove2.me/submissions/7f6ba98c-bd24-41a9-a62a-58a93efe31b2

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_Central
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_Tensor
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_CapelliWhittakerZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_WhittakerZeroStatement
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_casimir_tensV
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_casimir_tensVd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_isGlRep_tensV
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_isGlRep_tensVd


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
theorem _root_.solution : CapelliTensorStatement.{u} := by
  intro M _ _ n E hE
  exact ⟨isGlRep_tensV E hE, isGlRep_tensVd E hE, casimir_tensV E, casimir_tensVd E⟩
end ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
