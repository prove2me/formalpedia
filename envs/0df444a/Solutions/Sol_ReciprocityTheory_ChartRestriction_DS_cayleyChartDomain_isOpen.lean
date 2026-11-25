-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.cayleyChartDomain_isOpen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:22:40.85946+00:00
-- url     : https://prove2.me/submissions/a5632752-1fde-46e2-a118-53dfc7ab11db

import Definitions.Def_Formalism_RealPlaceAnalysis_Complexify
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CayleyChartDomainIsOpen

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
theorem _root_.solution (ε : Fin n → Bool) (g0 : Matrix (Fin n) (Fin n) ℂ) : IsOpen (cayleyChartDomain ε g0) := by
  show IsOpen {g : Matrix (Fin n) (Fin n) ℂ | (slmJi ε g0 * g + 1).det ≠ 0}
  exact isOpen_ne_fun ((continuous_const.matrix_mul continuous_id).add continuous_const).matrix_det
    continuous_const
end ReciprocityTheory.ChartRestriction.DS
