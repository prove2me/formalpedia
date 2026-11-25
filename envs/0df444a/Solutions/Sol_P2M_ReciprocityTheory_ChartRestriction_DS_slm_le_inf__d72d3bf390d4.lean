-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_DS_slm_le_inf__d72d3bf390d4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:51:30.472906+00:00
-- url     : https://prove2.me/submissions/efb5edc4-24b9-4b54-b90d-f88d5ba84626

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
theorem _root_.solution (N : ℕ) : (N : WithTop ℕ∞) ≤ ∞ := by
  first
  | exact_mod_cast (le_top : ((N : ℕ) : ℕ∞) ≤ ⊤)
  | (norm_cast; exact le_top)
  | exact WithTop.coe_le_coe.mpr le_top
  | simp
end ReciprocityTheory.ChartRestriction.DS
