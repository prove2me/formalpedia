-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.slm_le_inf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:25:29.67281+00:00
-- url     : https://prove2.me/submissions/c49227fc-3043-4a08-823a-8d12dc5b50e5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CayleyChartDomainIsOpen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_ContDiffOnZeroOfContinuousOn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Matrix
open scoped ContDiff
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {ε : Fin n → Bool}
local notation "JJ" => Formalism.REAL.Jm
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (N : ℕ) : (N : WithTop ℕ∞) + 1 ≤ ∞ := by
  first
  | exact_mod_cast (le_top : ((N + 1 : ℕ) : ℕ∞) ≤ ⊤)
  | (norm_cast; exact le_top)
  | exact WithTop.coe_le_coe.mpr le_top
  | simp
end ReciprocityTheory.ChartRestriction.DS
