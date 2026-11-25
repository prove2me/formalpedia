-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_ChartFormsRational_mem_of_mem_chartRing_7697125cad1f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:13:33.153806+00:00
-- url     : https://prove2.me/submissions/4a6c6d02-e35f-473a-a49c-d5d784afa907

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsChartFormsRational
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PChartDualRational
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PChartDetRatio
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PChartFormsRational

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ChartDualRational
noncomputable section
namespace GroundTheory.Heights₂.Heights.Inter
namespace ChartFormsRational
theorem _root_.solution {Ω : Type*} [Field Ω] {ι : Type*} (x : ι → Ω) (i : ι) {a : Ω}
    (ha : a ∈ chartRing ℤ x i) : a ∈ chartFunField x i := by
  induction ha using Algebra.adjoin_induction with
  | mem y hy => exact Subfield.subset_closure hy
  | algebraMap r =>
    rw [eq_intCast]
    exact intCast_mem _ r
  | add y z _ _ hy hz => exact add_mem hy hz
  | mul y z _ _ hy hz => exact mul_mem hy hz
end ChartFormsRational
end GroundTheory.Heights₂.Heights.Inter
