-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.slow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:48:25.545493+00:00
-- url     : https://prove2.me/submissions/f94573c0-50c8-41c5-afce-6dc7d151c627

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_TailInt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_PolynomialGrowthIntegrals
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_SlowWeightBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_PlanarKernelBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_OscillatoryBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_OsOf
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_Xi_slowWeightBound__2fa23c37e40b


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
theorem _root_.solution : SLOW := slowWeightBound'
end ReciprocityTheory.ChartRestriction.DS.Xi
