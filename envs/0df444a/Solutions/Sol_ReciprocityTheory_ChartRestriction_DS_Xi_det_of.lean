-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.det_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:00:33.877881+00:00
-- url     : https://prove2.me/submissions/ace612bf-0061-409c-8a6c-317d727e4541

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_XiRNonneg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HermitianLiftIdentities
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_XiIntStepOf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_detH


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
theorem _root_.solution (hB2 : InductiveHeisenbergInputs) : DET := detH hB2
end ReciprocityTheory.ChartRestriction.DS.Xi
