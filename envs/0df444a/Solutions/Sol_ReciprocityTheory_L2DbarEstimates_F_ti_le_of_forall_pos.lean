-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.ti_le_of_forall_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:15:44.413217+00:00
-- url     : https://prove2.me/submissions/7f8f06da-cc60-451c-b6cc-5a8d42972ca1

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_TestIneq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_ofReal
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_add


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.F
theorem _root_.solution (x c Y : ℝ≥0∞)
    (h : ∀ ε : ℝ, 0 < ε → x ≤ c * (ENNReal.ofReal (1 + ε) * Y)) : x ≤ c * Y := by
  have hc : Continuous fun ε : ℝ => ENNReal.ofReal (1 + ε) :=
    ENNReal.continuous_ofReal.comp (continuous_const.add continuous_id)
  have ht0 : Tendsto (fun ε : ℝ => ENNReal.ofReal (1 + ε)) (𝓝[>] 0) (𝓝 1) := by
    have h1 := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    simpa using h1
  have ht : Tendsto (fun ε : ℝ => ENNReal.ofReal (1 + ε) * (c * Y)) (𝓝[>] 0) (𝓝 (c * Y)) := by
    have h1 := ENNReal.Tendsto.mul_const (b := c * Y) ht0 (Or.inl one_ne_zero)
    simpa using h1
  exact ge_of_tendsto ht (eventually_nhdsWithin_of_forall fun ε hε => by
    calc x ≤ c * (ENNReal.ofReal (1 + ε) * Y) := h ε hε
      _ = ENNReal.ofReal (1 + ε) * (c * Y) := by ring)
end ReciprocityTheory.L2DbarEstimates.F
