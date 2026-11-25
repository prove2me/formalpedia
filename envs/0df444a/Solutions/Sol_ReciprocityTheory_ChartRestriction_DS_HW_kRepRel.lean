-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.kRepRel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:26:41.372651+00:00
-- url     : https://prove2.me/submissions/904f81f4-f8d6-4554-91c2-2f160477c7e0

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ContinuousRepresentations_DerivExistsAllPosStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_HasDerivAtRealOfComplex
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ContinuousRepresentations_RelOpCurve
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_KRep_kUnit_units
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_KRep_kRel_units

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
open scoped InnerProductSpace
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.HW
theorem _root_.solution : KRepRelStatement := fun _ _ R => ⟨R.kRel_units, R.kUnit_units⟩
end ReciprocityTheory.ChartRestriction.DS.HW
