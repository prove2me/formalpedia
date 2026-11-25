-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.slm_ret_inUJ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:34:45.477843+00:00
-- url     : https://prove2.me/submissions/98668882-08e3-4920-8754-f1ddb0e6961b

import Definitions.Def_Formalism_RealPlaceAnalysis_Complexify
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CayleyChartDomainIsOpen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_slm_inUJ_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_skewAdjointPart_isSkewAdjoint
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_slm_cay_inUJ

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
theorem _root_.solution {g0 : Matrix (Fin n) (Fin n) ℂ} (hg0 : Formalism.REAL.inUJ ε g0) :
    ∀ g ∈ slmV ε g0, Formalism.REAL.inUJ ε (slmRet ε g0 g) := fun g hg => slm_inUJ_mul hg0 (slm_cay_inUJ (skewAdjointPart_isSkewAdjoint ε _) hg.2)
end ReciprocityTheory.ChartRestriction.DS
