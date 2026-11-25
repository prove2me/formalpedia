-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.slm_V_open
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:47:50.453375+00:00
-- url     : https://prove2.me/submissions/43a61a70-f70a-443e-8334-b301f025a2a6

import Definitions.Def_Formalism_RealPlaceAnalysis_Complexify
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CayleyChartDomainIsOpen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_slm_X_cd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_cayleyChartDomain_isOpen

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
theorem _root_.solution (ε : Fin n → Bool) (g0 : Matrix (Fin n) (Fin n) ℂ) : IsOpen (slmV ε g0) :=
  ContinuousOn.isOpen_inter_preimage (f := fun g => (1 - slmX ε g0 g).det)
    ((continuous_id.matrix_det).comp_continuousOn (continuousOn_const.sub (slm_X_cd ε g0).continuousOn))
    (cayleyChartDomain_isOpen ε g0) isOpen_compl_singleton
end ReciprocityTheory.ChartRestriction.DS
