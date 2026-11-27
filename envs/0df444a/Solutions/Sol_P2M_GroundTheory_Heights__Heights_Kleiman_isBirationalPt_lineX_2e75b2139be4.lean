-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_isBirationalPt_lineX_2e75b2139be4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:02:40.762015+00:00
-- url     : https://prove2.me/submissions/dd41afe4-d00a-485f-8041-d3f58d3eacd2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_AlgebraMapMemChartRingLine
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_algebraMap_mem_chartRing_line_3298f58654f8

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial Filter
noncomputable section
universe u v w
variable (k : Type u) [Field k]
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution : IsBirationalPt k (lineX k) := by
  intro s
  have hd : algebraMap (Polynomial k) (RatFunc k) s.denom ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr s.denom_ne_zero
  refine ⟨lineChart0 k, algebraMap (Polynomial k) (RatFunc k) s.num,
    algebraMap (Polynomial k) (RatFunc k) s.denom, algebraMap_mem_chartRing_line k _,
    algebraMap_mem_chartRing_line k _, hd, ?_⟩
  exact ((div_eq_iff hd).mp (RatFunc.num_div_denom s)).symm
end GroundTheory.Heights₂.Heights.Kleiman
