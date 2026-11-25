-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_PtsRegLimit_tendsto_half_log_202190eeb978
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:15:43.730119+00:00
-- url     : https://prove2.me/submissions/170e1982-423a-4b3a-a8c7-08b1572c5f60

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StPtsRegLimit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StPtsAbsIntegrable
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPtsRegLimit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo
namespace GroundTheory.Heights₂.Heights.Inter
namespace PtsRegLimit
theorem _root_.solution {x : ℝ} (hx : x ≠ 0) :
    Tendsto (fun ε : ℝ => Real.log (x ^ 2 + ε) / 2) (𝓝[>] 0) (𝓝 (Real.log x)) := by
  have h2 : x ^ 2 + 0 ≠ 0 := by rw [add_zero]; exact pow_ne_zero 2 hx
  have hc : ContinuousAt (fun ε : ℝ => Real.log (x ^ 2 + ε) / 2) 0 :=
    ((continuousAt_const.add continuousAt_id).log h2).div_const 2
  have hv : Real.log (x ^ 2 + 0) / 2 = Real.log x := by
    rw [add_zero, Real.log_pow]; push_cast; ring
  rw [← hv]
  exact hc.tendsto.mono_left nhdsWithin_le_nhds
end PtsRegLimit
end GroundTheory.Heights₂.Heights.Inter
