-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_PtsRegLimit_abs_half_log_le_9e14d95ff747
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:15:39.151528+00:00
-- url     : https://prove2.me/submissions/f35f1bf8-ea74-476e-a078-596b97a07ab7

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
theorem _root_.solution {x ε : ℝ} (hx : x ≠ 0) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    |Real.log (x ^ 2 + ε) / 2| ≤ |Real.log x| + |Real.log (x ^ 2 + 1) / 2| := by
  have h2 : 0 < x ^ 2 := lt_of_le_of_ne (sq_nonneg x) (Ne.symm (pow_ne_zero 2 hx))
  have hlo : Real.log x ≤ Real.log (x ^ 2 + ε) / 2 := by
    have : Real.log x = Real.log (x ^ 2) / 2 := by rw [Real.log_pow]; push_cast; ring
    rw [this]
    exact div_le_div_of_nonneg_right (Real.log_le_log h2 (by linarith)) (by norm_num)
  have hhi : Real.log (x ^ 2 + ε) / 2 ≤ Real.log (x ^ 2 + 1) / 2 :=
    div_le_div_of_nonneg_right (Real.log_le_log (by linarith) (by linarith)) (by norm_num)
  rw [abs_le]
  constructor
  · linarith [neg_abs_le (Real.log x), abs_nonneg (Real.log (x ^ 2 + 1) / 2)]
  · linarith [le_abs_self (Real.log (x ^ 2 + 1) / 2), abs_nonneg (Real.log x)]
end PtsRegLimit
end GroundTheory.Heights₂.Heights.Inter
