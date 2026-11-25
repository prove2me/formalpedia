-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.subgroupData.qv_cont
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:19:54.385936+00:00
-- url     : https://prove2.me/submissions/0218e149-0c2a-4abc-9ba9-bc74243de057

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_TailInt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_PolynomialGrowthIntegrals

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open ReciprocityTheory.ChartRestriction.DS.Xi.subgroupData
namespace ReciprocityTheory.ChartRestriction.DS.Xi.subgroupData
theorem _root_.solution (c : Fin 3 → ℂ) : Continuous (qv c) := by
  unfold qv; fun_prop
end ReciprocityTheory.ChartRestriction.DS.Xi.subgroupData
