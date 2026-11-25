-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.ArchimedeanConeVolume.volume_cone0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:43:04.156983+00:00
-- url     : https://prove2.me/submissions/edba1100-1cb3-408d-99a1-89e84c8f77b2

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_KappaA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LintegralIoiOfRealMul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_ArchimedeanConeVolume_lintegral_coneFun
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_ArchimedeanConeVolume_norm_eq_sqrt_coord
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_ArchimedeanConeVolume_measurableSet_cone0

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set Real
open scoped ENNReal Pointwise
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.ArchimedeanConeVolume
namespace ReciprocityTheory.ChartRestriction.G.AI.ArchimedeanConeVolume
theorem _root_.solution {s : Set ℝ} (hs : MeasurableSet s) :
    volume {y : E3 | 0 < ‖y‖ ∧ ‖y‖ < 1 ∧ y 0 / ‖y‖ ∈ s} =
      coneConst * volume (s ∩ Ioo (-1 : ℝ) 1) := by
  rw [← lintegral_indicator_one (measurableSet_cone0 hs)]
  have h : ∀ y : E3, {y : E3 | 0 < ‖y‖ ∧ ‖y‖ < 1 ∧ y 0 / ‖y‖ ∈ s}.indicator 1 y =
      coneFun (s.indicator 1) (y 0) ((y 1) ^ 2 + (y 2) ^ 2) := by
    intro y
    have hn := norm_eq_sqrt_coord y
    set S := y 0 ^ 2 + (y 1 ^ 2 + y 2 ^ 2) with hS
    have hS0 : 0 ≤ S := by positivity
    unfold coneFun
    by_cases hc : 0 < S ∧ S < 1
    · rw [if_pos hc]
      have h0 : 0 < ‖y‖ := by rw [hn]; exact Real.sqrt_pos.2 hc.1
      have h1 : ‖y‖ < 1 := by
        rw [hn, ← Real.sqrt_one]; exact Real.sqrt_lt_sqrt hS0 hc.2
      by_cases hy : y 0 / ‖y‖ ∈ s
      · rw [indicator_of_mem (show y ∈ {y : E3 | 0 < ‖y‖ ∧ ‖y‖ < 1 ∧ y 0 / ‖y‖ ∈ s} from
          ⟨h0, h1, hy⟩), ← hn, indicator_of_mem hy]
        rfl
      · rw [indicator_of_notMem (fun h => hy h.2.2), ← hn, indicator_of_notMem hy]
    · rw [if_neg hc, indicator_of_notMem]
      rintro ⟨h0, h1, -⟩
      apply hc
      rw [hn] at h0 h1
      refine ⟨Real.sqrt_pos.1 h0, ?_⟩
      nlinarith [Real.sq_sqrt hS0, Real.sqrt_nonneg S]
  simp_rw [h]
  rw [lintegral_coneFun (s.indicator 1) (measurable_one.indicator hs), lintegral_indicator_one hs,
    Measure.restrict_apply hs, coneConst]
end ReciprocityTheory.ChartRestriction.G.AI.ArchimedeanConeVolume
