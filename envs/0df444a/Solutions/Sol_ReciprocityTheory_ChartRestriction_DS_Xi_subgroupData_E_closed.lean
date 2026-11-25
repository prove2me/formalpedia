-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.subgroupData.E_closed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:27:51.14708+00:00
-- url     : https://prove2.me/submissions/ba860c33-35b2-4a9d-aa3a-fca8001ab7fe

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_TailInt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_PolynomialGrowthIntegrals
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_subgroupData_qv_cont

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
theorem _root_.solution (c : Fin 3 → ℂ) (la : ℝ) : IsClosed {t | t ∈ Icc (1:ℝ) 2 ∧ ‖qv c t‖ ≤ la} :=
  isClosed_Icc.inter (isClosed_le (continuous_norm.comp (qv_cont c)) continuous_const)
end ReciprocityTheory.ChartRestriction.DS.Xi.subgroupData
