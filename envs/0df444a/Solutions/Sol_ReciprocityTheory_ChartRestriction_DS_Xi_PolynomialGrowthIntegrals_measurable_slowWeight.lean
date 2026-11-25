-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.PolynomialGrowthIntegrals.measurable_slowWeight
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:19:06.765464+00:00
-- url     : https://prove2.me/submissions/8ed8f1e9-e9a3-4b42-af43-e622a706b560

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_TailInt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_SlowWeightBound

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
open ReciprocityTheory.ChartRestriction.DS.Xi.PolynomialGrowthIntegrals
namespace ReciprocityTheory.ChartRestriction.DS.Xi.PolynomialGrowthIntegrals
theorem _root_.solution {n : ℕ} (t A b : Fin n → ℝ) : Measurable (slowly t A b) := by
  unfold slowly
  fun_prop
end ReciprocityTheory.ChartRestriction.DS.Xi.PolynomialGrowthIntegrals
