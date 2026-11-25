-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.coefStep_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:05:03.279341+00:00
-- url     : https://prove2.me/submissions/6579f047-f6f6-4c4c-b9e2-bf92877d5960

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_XiRNonneg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HermitianLiftIdentities
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_XiIntStepOf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_CB_coefStepC


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
namespace ReciprocityTheory.ChartRestriction.DS.Xi
theorem _root_.solution (hB2 : InductiveHeisenbergInputs) (hT : TBoth) (hD : DET) : CoefStep := CB.coefStepC hB2 hT hD
end ReciprocityTheory.ChartRestriction.DS.Xi
